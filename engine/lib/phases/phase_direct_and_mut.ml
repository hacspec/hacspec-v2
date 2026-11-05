open! Prelude

module%inlined_contents Make
    (FA :
      Features.T
        with type raw_pointer = Features.Off.raw_pointer
         and type mutable_pointer = Features.Off.mutable_pointer) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.On.Mutable_variable
    include Features.On.Arbitrary_lhs
    include Features.On.Nontrivial_lhs
    include Features.Off.Mutable_reference
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  (** Reference to a fresh local ident (item-wise) *)
  let out_var = ref Local_ident.{ id = mk_id Expr 0; name = "out" }

  module Implem : ImplemT.T = struct
    let metadata = metadata

    let hax_core_extraction =
      Sys.getenv "HAX_CORE_EXTRACTION_MODE"
      |> [%equal: string option] (Some "on")

    module S = struct
      include Features.SUBTYPE.Id
      include Features.SUBTYPE.On.Mutable_variable
      include Features.SUBTYPE.On.Nontrivial_lhs
      include Features.SUBTYPE.On.Arbitrary_lhs
    end

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    let ( let* ) x f = Option.bind ~f x

    module Place = UA.Place

    let expect_mut_borrow_of_place_or_pure_expr (e : A.expr) :
        (Place.t, A.expr) Either.t option =
      let e = UA.Mappers.normalize_borrow_mut#visit_expr () e in
      let e = UA.remove_unsize e in
      let* e = UA.Expect.mut_borrow e in
      Option.some
      @@
      match
        let* p = Place.of_expr e in
        Some (Place.skip_allowed_deref_mut p)
      with
      | Some place -> Either.First place
      | None -> Second e

    [%%inline_defs dmutability + dsafety_kind]

    let rec dty (span : span) (ty : A.ty) : B.ty =
      match ty with
      | [%inline_arms "dty.*" - TRef] -> auto
      | TRef { mut = Mutable _; typ; _ } ->
          if hax_core_extraction then
            TApp
              {
                ident =
                  Global_ident.of_name ~value:false Rust_primitives__hax__MutRef;
                args = [ GType (dty span typ) ];
              }
          else Error.raise { kind = UnallowedMutRef; span }
      | TRef { witness; typ; mut = Immutable as mut; region } ->
          TRef { witness; typ = dty span typ; mut; region }

    and dborrow_kind (_span : span) (borrow_kind : A.borrow_kind) :
        B.borrow_kind =
      match borrow_kind with
      | [%inline_arms "dborrow_kind.*" - Mut] -> auto
      | Mut _ -> Shared

    (* TODO: refactor (see #316) *)
    and place_to_lhs (p : Place.t) : B.lhs =
      let typ = dty p.span p.typ in
      match p.place with
      | LocalVar var -> LhsLocalVar { var; typ }
      | VecRef inner ->
          LhsVecRef
            {
              e = place_to_lhs inner;
              typ;
              witness = Features.On.nontrivial_lhs;
            }
      | FieldProjection { place; projector } ->
          let e = place_to_lhs place in
          LhsFieldAccessor
            { witness = Features.On.nontrivial_lhs; field = projector; typ; e }
      | IndexProjection { place; index } ->
          let e = place_to_lhs place in
          let index = dexpr index in
          LhsArrayAccessor
            { e; typ; index; witness = Features.On.nontrivial_lhs }
      | _ ->
          let e = Place.to_expr p |> dexpr in
          LhsArbitraryExpr { witness = Features.On.arbitrary_lhs; e }

    and translate_app (span : span) (otype : A.ty) (f : A.expr)
        (raw_args : A.expr list) (generic_args : B.generic_value list)
        (trait : (B.impl_expr * B.generic_value list) option) bounds_impls :
        B.expr =
      (* `otype` and `_otype` (below) are supposed to be the same
         type, but sometimes `_otype` is less precise (i.e. an associated
         type while a concrete type is available) *)
      let arg_types, _otype =
        UA.Expect.arrow f.typ
        |> Option.value_or_thunk ~default:(fun _ ->
            Error.assertion_failure span "expected an arrow type here")
      in
      (* each input of `f` is either:
         - of type `&mut _` and then the value fed to f should either be a place or a "pure" expression;
         - of another type, and then the value can be anything.
      *)
      let args : ((Place.t, A.expr) Either.t * bool) list =
        (match List.zip arg_types raw_args with
          | Ok inputs -> inputs
          | _ -> Error.assertion_failure span "application: bad arity")
        |> List.map ~f:(fun (typ, (arg : A.expr)) ->
            if UA.Expect.mut_ref typ |> Option.is_some then
              (* the argument of the function is mutable *)
              let v =
                expect_mut_borrow_of_place_or_pure_expr arg
                |> Option.value_or_thunk ~default:(fun _ ->
                    Error.raise { kind = ExpectedMutRef; span = arg.span })
              in
              (v, true)
            else (Either.second arg, false))
      in
      (* `mutargs`: all mutable borrows fed to `f` *)
      let mutargs : (Place.t, A.expr) Either.t list =
        args |> List.filter ~f:snd |> List.map ~f:fst
      in
      match mutargs with
      | [] ->
          (* there is no mutation, we can reconstruct the expression right away *)
          let f, typ = (dexpr f, dty span otype) in
          let args = List.map ~f:dexpr raw_args in
          B.
            {
              e = B.App { f; args; generic_args; trait; bounds_impls };
              typ;
              span;
            }
      | _ -> (
          (* TODO: when LHS are better (issue #222), compress `p1 = tmp1; ...; pN = tmpN` in `(p1...pN) = ...` *)
          (* we are generating:
             ```
             let (tmp1, …, tmpN, out) = ⟨f⟩(⟨…un-&mut args⟩);
             p1 = tmp1;
                 …
             pN = tmpN;
             out
             ```
          *)
          let ty_of_either : (Place.t, A.expr) Either.t -> A.ty = function
            | First p -> p.typ
            | Second e -> e.typ
          in
          let span_of_either : (Place.t, A.expr) Either.t -> span = function
            | First p -> p.span
            | Second e -> e.span
          in
          let b_ty_of_either : (Place.t, A.expr) Either.t -> B.ty = function
            | First p -> dty p.span p.typ
            | Second e -> dty e.span e.typ
          in

          let mutargs : ((local_ident * B.lhs) option * (B.ty * span)) list =
            let to_ident_lhs i = function
              | Either.First (place : Place.t) ->
                  let var =
                    Local_ident.
                      { id = mk_id Expr 0; name = "tmp" ^ Int.to_string i }
                  in
                  Some (var, place_to_lhs place)
              | _ -> None
            in
            let to_ty_span x =
              let span = span_of_either x in
              (dty span (ty_of_either x), span)
            in
            List.mapi ~f:(fun i -> to_ident_lhs i &&& to_ty_span) mutargs
          in

          let out_var = !out_var in
          let otype = dty f.span otype in
          let pat =
            let out =
              if UB.is_unit_typ otype then []
              else [ UB.make_var_pat out_var otype f.span ]
            in
            List.map
              ~f:(function
                | Some (var, _), (ty, span) -> UB.make_var_pat var ty span
                | None, (typ, span) -> UB.M.pat_PWild ~typ ~span)
              mutargs
            @ out
            |> UB.make_tuple_pat
          in
          let f_call =
            let f : B.expr =
              let typ =
                B.TArrow (List.map ~f:(fst >> b_ty_of_either) args, pat.typ)
              in
              B.{ span = f.span; typ; e = dexpr' f.span f.e }
            in
            let unmut_args =
              args
              |> List.map
                   ~f:
                     ( fst >> function
                       | Either.First p -> Place.to_expr p
                       | Either.Second e -> e )
              |> List.map ~f:dexpr
            in
            B.
              {
                e =
                  App
                    { f; args = unmut_args; generic_args; trait; bounds_impls };
                typ = pat.typ;
                span = pat.span;
              }
          in
          (* when lhs type accepts tuple (issue #222), assigns will be an option instead of a list *)
          let assigns =
            let flatten (o, meta) = Option.map o ~f:Fn.(id &&& const meta) in
            List.filter_map ~f:flatten mutargs
            |> List.map ~f:(fun ((var, lhs), (typ, span)) ->
                let e = B.{ e = LocalVar var; span; typ } in
                let witness = Features.On.mutable_variable in
                B.{ e = Assign { lhs; e; witness }; span; typ = UB.unit_typ })
          in
          (* TODO: this should be greatly simplified when `lhs` type will accept tuples (issue #222) *)
          (* The call returns the value of the place alone only when it takes
             no other `&mut`, such as a temporary. *)
          match assigns with
          | [ { e = Assign { lhs; witness; _ }; span; typ } ]
            when UB.is_unit_typ otype && List.length mutargs = 1 ->
              { e = Assign { lhs; e = f_call; witness }; span; typ }
              |> extract_vec_ref
          | _ ->
              let body =
                let init =
                  if UB.is_unit_typ otype then UB.unit_expr f.span
                  else B.{ typ = otype; span = f.span; e = LocalVar out_var }
                in
                assigns
                |> List.map ~f:extract_vec_ref
                |> List.fold_right ~init ~f:UB.make_seq
              in
              let r = UB.make_let pat f_call body in
              r)

    and extract_vec_ref : B.expr -> B.expr = function
      | { e = Assign { lhs = LhsVecRef { e = lhs; _ }; witness; e }; span; typ }
        ->
          {
            e =
              Assign
                {
                  lhs;
                  e = UB.call Alloc__slice__Impl__to_vec [ e ] e.span typ;
                  witness;
                };
            span;
            typ;
          }
      | e -> e

    and dexpr' (span : span) (e : A.expr') : B.expr' =
      match e with
      | [%inline_arms "dexpr'.*" - Borrow - App] -> auto
      | Borrow { kind; e; witness } ->
          Borrow
            {
              kind =
                (match kind with
                | Mut _ -> Error.raise { kind = UnallowedMutRef; span }
                | Shared -> B.Shared
                | Unique -> B.Unique);
              e = dexpr e;
              witness;
            }
      | App _ ->
          Error.assertion_failure span
            "should have been handled by dexpr_unwrapped"

    and dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | App { f; args; generic_args; trait; bounds_impls } ->
          let dgeneric_args = List.map ~f:(dgeneric_value span) in
          let generic_args = dgeneric_args generic_args in
          let trait = Option.map ~f:(dimpl_expr span *** dgeneric_args) trait in
          let bounds_impls = List.map ~f:(dimpl_expr span) bounds_impls in
          translate_app span expr.typ f args generic_args trait bounds_impls
      | _ ->
          let e = dexpr' span expr.e in
          B.{ e; typ = dty expr.span expr.typ; span = expr.span }
    [@@inline_ands bindings_of dexpr]

    [%%inline_defs
    dgeneric_param + dgeneric_constraint + dgenerics + dparam + dvariant
    + dtrait_item' + dimpl_item']

    let rec ditem' span (item : A.item') : B.item' =
      let vars = UA.Reducers.collect_local_idents#visit_item' () item in
      out_var := UA.fresh_local_ident_in (Set.to_list vars) "out";
      [%inline_body ditem'] span item
    [@@inline_ands "Item.*"]
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

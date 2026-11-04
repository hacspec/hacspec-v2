open! Prelude

module%inlined_contents Make (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.On.Question_mark
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
      include Features.SUBTYPE.On.Question_mark
    end

    (** The local names of the item being translated, which the binders
        introduced for [?] avoid. *)
    let taken_names = ref (Set.empty (module String))

    module QuestionMarks = struct
      [@@@warning "-9"]

      open A

      (** The types supported for [e] in a [e?] expression *)
      type qm_kind = QMResult of { success : ty; error : ty } | QMOption of ty

      (** Interpret a type [t] as a [qm_kind] *)
      let qm_kind_of_typ span (t : ty) : qm_kind =
        let is_result = Global_ident.eq_name Core__result__Result in
        let is_option = Global_ident.eq_name Core__option__Option in
        match t with
        | TApp { ident; args = [ GType s; GType e ] } when is_result ident ->
            QMResult { success = s; error = e }
        | TApp { ident; args = [ GType s ] } when is_option ident -> QMOption s
        | _ ->
            Error.assertion_failure span
              ("expected something of type Option<_> or Result<_, _>, instead, \
                got: "
              ^ [%show: ty] t)

      (** Expects [impl] to be an impl. expr. for the trait
          `std::ops::FromResidual` for the type [Result<_, _>], and extract its
          parent [From] impl expr *)
      let expect_residual_impl_result (impl : impl_expr) : impl_expr option =
        match impl with
        | {
         kind = ImplApp { args = [ from_impl ]; _ };
         goal =
           {
             trait;
             args =
               [
                 GType (TApp { ident = arg1; _ });
                 GType (TApp { ident = arg2; _ });
               ];
           };
        }
          when Concrete_ident.eq_name Core__ops__try_trait__FromResidual trait
               && Global_ident.eq_name Core__result__Result arg1
               && Global_ident.eq_name Core__result__Result arg2 ->
            Some from_impl
        | _ -> None

      (** Expects [t] to be [Result<S, E>], and returns [(S, E)] *)
      let expect_result_type (t : ty) : (ty * ty) option =
        match t with
        | TApp { ident; args = [ GType s; GType e ] }
          when Global_ident.eq_name Core__result__Result ident ->
            Some (s, e)
        | _ -> None

      (** Construct [Result<S,E>] *)
      let make_result_type (success : ty) (error : ty) : ty =
        let ident = Global_ident.of_name ~value:false Core__result__Result in
        TApp { ident; args = [ GType success; GType error ] }

      (** Retype a [Err::<_, E>(x)] literal, as [Err::<success, E>(x)] *)
      let retype_err_literal (e : expr) (success : ty) (error : ty) =
        match e.e with
        | Construct { constructor; _ }
          when Global_ident.eq_name Core__result__Result__Err constructor ->
            { e with typ = make_result_type success error }
        | _ -> e

      let convert_from (e : expr) (error_dest : ty) impl : expr option =
        let error_src = e.typ in
        let* impl = expect_residual_impl_result impl in
        let*? _ = [%eq: ty] error_src error_dest |> not in
        let from_typ = TArrow ([ error_src ], error_dest) in
        let impl_generic_args = [ GType error_dest; GType error_src ] in
        Some
          (UA.call ~impl_generic_args ~impl Core__convert__From__from [ e ]
             e.span from_typ)

      (** [map_err e error_dest impl] creates the expression [e.map_err(from)]
          with the proper types and impl informations. *)
      let map_err (e : expr) (error_dest : ty) impl : expr option =
        let* success, error_src = expect_result_type e.typ in
        let* impl = expect_residual_impl_result impl in
        let from_typ = TArrow ([ error_src ], error_dest) in
        let from = UA.call ~impl Core__convert__From__from [] e.span from_typ in
        let call =
          UA.call Core__result__Impl__map_err [ e; from ] e.span
            (make_result_type success error_dest)
        in
        Some call

      let mk_pconstruct ~is_struct ~is_record ~span ~typ
          (constructor : Concrete_ident_generated.t)
          (fields : (Concrete_ident_generated.t * pat) list) =
        let constructor = Global_ident.of_name ~value:true constructor in
        let fields =
          List.map
            ~f:(fun (field, pat) ->
              let field = Global_ident.of_name ~value:true field in
              { field; pat })
            fields
        in
        let p = PConstruct { constructor; fields; is_record; is_struct } in
        { p; span; typ }

      (** [extract e] returns [Some (x, ty)] if [e] was a `y?` desugared by
          rustc. `y` is `x` plus possibly a coercion. [ty] is the return type of
          the function. *)
      let extract (e : expr) : expr option =
        let extract_return (e : expr) =
          match e.e with
          | Return
              {
                e =
                  {
                    e =
                      App
                        {
                          f = { e = GlobalVar f };
                          args = [ { e = LocalVar residual_var; _ } ];
                          trait = Some (impl, _);
                        };
                    typ = return_typ;
                    _;
                  };
                witness;
              } ->
              Some (f, residual_var, return_typ, impl, witness)
          | _ -> None
        in
        let extract_pat_app_bd (p : pat) : (global_ident * local_ident) option =
          match p.p with
          | PConstruct
              {
                constructor = name;
                fields =
                  [
                    {
                      pat =
                        {
                          p =
                            PBinding { mut = Immutable; var; subpat = None; _ };
                          _;
                        };
                      _;
                    };
                  ];
                _;
              } ->
              Some (name, var)
          | _ -> None
        in
        match e.e with
        | Match
            {
              scrutinee =
                { e = App { f = { e = GlobalVar n; _ }; args = [ expr ] }; _ };
              arms =
                [
                  { arm = { arm_pat = pat_break; body }; _ };
                  { arm = { arm_pat = pat_continue; body = continue_expr }; _ };
                ];
            }
          when Global_ident.eq_name Core__ops__try_trait__Try__branch n ->
            let* body =
              UA.Expect.concrete_app1 Rust_primitives__hax__never_to_any body
            in
            let* f, residual_var, fun_return_typ, residual_impl, return_witness
                =
              extract_return body
            in
            let* f_break, residual_var' = extract_pat_app_bd pat_break in
            let* f_continue, continue_var' = extract_pat_app_bd pat_continue in
            let continue_expr =
              Option.value
                (UA.Expect.borrow continue_expr)
                ~default:continue_expr
            in
            let continue_expr = UA.unbox_underef_expr continue_expr in
            let* continue_var = UA.Expect.local_var continue_expr in
            let*? _ = [%equal: local_ident] residual_var residual_var' in
            let*? _ = [%equal: local_ident] continue_var continue_var' in
            let*? _ =
              Global_ident.eq_name Core__ops__control_flow__ControlFlow__Break
                f_break
              && Global_ident.eq_name
                   Core__ops__control_flow__ControlFlow__Continue f_continue
              && Global_ident.eq_name
                   Core__ops__try_trait__FromResidual__from_residual f
            in
            let kind = qm_kind_of_typ e.span in
            let span = expr.span in
            let mk_var name : local_ident =
              let name =
                if Set.mem !taken_names name then
                  UA.Capture.fresh_name !taken_names name
                else name
              in
              { name; id = Local_ident.mk_id Expr (-1) }
            in
            let mk_cons =
              mk_pconstruct ~is_struct:false ~is_record:false ~span
                ~typ:expr.typ
            in
            let expr =
              match (kind expr.typ, kind fun_return_typ) with
              | ( QMResult { error = local_err; success = local_success },
                  QMResult { error = return_err; _ } ) ->
                  let var_ok, var_err = (mk_var "ok", mk_var "err") in
                  let arm_ok : A.arm =
                    let pat = UA.make_var_pat var_ok local_success span in
                    let arm_pat =
                      mk_cons Core__result__Result__Ok
                        [ (Core__result__Result__Ok__0, pat) ]
                    in
                    let body =
                      { typ = local_success; e = LocalVar var_ok; span }
                    in
                    { arm = { arm_pat; body; guard = None }; span }
                  in
                  let arm_err =
                    let pat = UA.make_var_pat var_err local_err span in
                    let arm_pat =
                      mk_cons Core__result__Result__Err
                        [ (Core__result__Result__Err__0, pat) ]
                    in
                    let err = { typ = local_err; e = LocalVar var_err; span } in
                    let err =
                      convert_from err return_err residual_impl
                      |> Option.value ~default:err
                    in
                    let err =
                      UA.call_Constructor Core__result__Result__Err false
                        [ err ] e.span fun_return_typ
                    in
                    let e = Return { e = err; witness = return_witness } in
                    let return = { typ = local_success; e; span } in
                    { arm = { arm_pat; body = return; guard = None }; span }
                  in
                  let arms, typ = ([ arm_ok; arm_err ], local_success) in
                  { e = Match { scrutinee = expr; arms }; typ; span }
              | QMOption local_success, QMOption _ ->
                  let var_some = mk_var "some" in
                  let arm_some : A.arm =
                    let pat = UA.make_var_pat var_some local_success span in
                    let arm_pat =
                      mk_cons Core__option__Option__Some
                        [ (Core__option__Option__Some__0, pat) ]
                    in
                    let body =
                      { typ = local_success; e = LocalVar var_some; span }
                    in
                    { arm = { arm_pat; body; guard = None }; span }
                  in
                  let arm_none =
                    let arm_pat = mk_cons Core__option__Option__None [] in
                    let none =
                      UA.call_Constructor Core__option__Option__None false []
                        e.span fun_return_typ
                    in
                    let e = Return { e = none; witness = return_witness } in
                    let return = { typ = local_success; e; span } in
                    { arm = { arm_pat; body = return; guard = None }; span }
                  in
                  let arms, typ = ([ arm_some; arm_none ], local_success) in
                  { e = Match { scrutinee = expr; arms }; typ; span }
              | _ ->
                  Error.assertion_failure e.span
                    "expected expr.typ and fun_return_typ to be both Options \
                     or both Results"
            in
            Some expr
        | _ -> None
    end

    [%%inline_defs dmutability + dsafety_kind]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      QuestionMarks.extract expr |> Option.value ~default:expr
      |> [%inline_body dexpr_unwrapped]
    [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*" - ditems]

    let ditems (items : A.item list) : B.item list =
      List.concat_map items ~f:(fun item ->
          taken_names := UA.Capture.all_names#visit_item () item;
          ditem item)
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

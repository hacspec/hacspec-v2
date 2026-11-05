(** This phase removes `return`s in exit position. Inside loops, it replaces
    `return`, `break` and `continue` (in exit position) by their encoding in the
    `ControlFlow` enum. It replaces another expression in exit position by an
    equivalent `continue`. This phase should comae after `RewriteControlFlow` to
    ensure all control flow is in exit position. *)

open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.On.Fold_like_loop
    include Features.Off.Early_exit
    include Features.Off.Break
    include Features.Off.Continue
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
    end

    (* break_type is "by default" unit since there always is a (possibly implicit) break type *)
    type loop_info = { return_type : A.ty option; break_type : A.ty option }

    let has_return =
      let module Visitors = Ast_visitors.Make (F) in
      object (self)
        inherit [_] Visitors.reduce as super
        method zero = { return_type = None; break_type = None }

        method plus li1 li2 =
          {
            return_type = Option.first_some li1.return_type li2.return_type;
            break_type = Option.first_some li1.break_type li2.break_type;
          }

        method! visit_expr' () e =
          match e with
          | Return { e; _ } -> { return_type = Some e.typ; break_type = None }
          | Break { e; _ } -> { return_type = None; break_type = Some e.typ }
          (* We should avoid catching breaks of a nested
             loops as they could have different types. *)
          | Loop { body; _ } ->
              {
                return_type = (self#visit_expr () body).return_type;
                break_type = None;
              }
          | Closure _ -> self#zero
          | _ -> super#visit_expr' () e
      end

    let visitor =
      let module Visitors = Ast_visitors.Make (F) in
      object (self)
        inherit [_] Visitors.map as _super

        method! visit_expr (in_loop : (loop_info * A.ty) option) e =
          let span = e.span in
          match (e.e, in_loop) with
          | Return { e; _ }, None -> e
          (* we know [e] is on an exit position: the return is
             thus useless, we can skip it *)
          | Let { monadic = None; lhs; rhs; body }, _ ->
              let body = self#visit_expr in_loop body in
              {
                e with
                e = Let { monadic = None; lhs; rhs; body };
                typ = body.typ;
              }
              (* If a let expression is an exit node, then it's body
                 is as well *)
          | Match { scrutinee; arms }, _ ->
              let arms = List.map ~f:(self#visit_arm in_loop) arms in
              let typ =
                match arms with { arm; _ } :: _ -> arm.body.typ | [] -> e.typ
              in
              { e with e = Match { scrutinee; arms }; typ }
          | If { cond; then_; else_ }, _ ->
              let then_ = self#visit_expr in_loop then_ in
              let else_ = Option.map ~f:(self#visit_expr in_loop) else_ in
              { e with e = If { cond; then_; else_ }; typ = then_.typ }
          | Return { e; _ }, Some ({ return_type; break_type }, acc_type) ->
              UA.M.expr_Constructor_CF ~return_type ~span ~break_type ~e
                ~acc:{ e with typ = acc_type } `Return
          | ( Break { e; acc = Some (acc, _); _ },
              Some ({ return_type; break_type }, _) ) ->
              UA.M.expr_Constructor_CF ~return_type ~span ~break_type ~e ~acc
                `Break
          | ( Continue { acc = Some (acc, _); _ },
              Some ({ return_type = None; break_type = None }, _) ) ->
              acc
          | ( Continue { acc = Some (acc, _); _ },
              Some ({ return_type; break_type }, _) ) ->
              UA.M.expr_Constructor_CF ~return_type ~span ~break_type ~acc
                `Continue
          | _, Some ({ return_type; break_type }, _)
            when Option.is_some return_type || Option.is_some break_type ->
              UA.M.expr_Constructor_CF ~return_type ~span ~break_type ~acc:e
                `Continue
          | _ -> e
        (** The invariant here is that [visit_expr] is called only on
            expressions that are on exit positions. [visit_expr] is first called
            on root expressions, which are (by definition) exit nodes. Then,
            [visit_expr] itself makes recursive calls to sub expressions that
            are themselves in exit nodes. **)
      end

    let closure_visitor =
      let module Visitors = Ast_visitors.Make (F) in
      object (self)
        inherit [_] Visitors.map as super

        method! visit_expr' () e =
          match e with
          | Closure ({ body; _ } as closure) ->
              let body = self#visit_expr () body |> visitor#visit_expr None in
              Closure { closure with body }
          | _ -> super#visit_expr' () e
      end

    [%%inline_defs dmutability + dsafety_kind]

    let rec dexpr' (span : span) (expr : A.expr') : B.expr' =
      match expr with
      | [%inline_arms "dexpr'.*" - Return - Break - Continue - Loop] -> auto
      | Return _ | Break _ | Continue _ ->
          Error.assertion_failure span
            "Return/Break/Continue are expected to be gone as this point"
      | Loop { body; kind; state; label; witness; _ } ->
          let control_flow_type = has_return#visit_expr () body in
          let control_flow =
            match control_flow_type with
            | { return_type = Some _; _ } ->
                Some (B.BreakOrReturn, Features.On.fold_like_loop)
            | { break_type = Some _; _ } ->
                Some (BreakOnly, Features.On.fold_like_loop)
            | _ -> None
          in
          let acc_type =
            match body.typ with
            | TApp { ident; args = [ GType _; GType continue_type ] }
              when Ast.Global_ident.equal ident
                     (Ast.Global_ident.of_name ~value:false
                        Core__ops__control_flow__ControlFlow) ->
                continue_type
            | _ -> body.typ
          in
          let body =
            visitor#visit_expr (Some (control_flow_type, acc_type)) body
            |> dexpr
          in
          let kind = dloop_kind span kind in
          let state = Option.map ~f:(dloop_state span) state in
          Loop { body; control_flow; kind; state; label; witness }
    [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*" - ditems]

    let ditems (items : A.item list) : B.item list =
      List.concat_map items
        ~f:(visitor#visit_item None >> closure_visitor#visit_item () >> ditem)
  end

  include Implem
end
[@@add "subtype.ml"]

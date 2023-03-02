(* type on = unit [@@deriving show, yojson, eq] *)
(* type off = | [@@deriving show, yojson, eq] *)

[%%declare_features
loop,
  for_loop,
  continue,
  mutable_variable,
  mutable_reference,
  mutable_pointer,
  reference,
  slice,
  raw_pointer,
  early_exit,
  macro,
  as_pattern,
  arbitrary_lhs,
  lifetime,
  monadic_action,
  monadic_binding]

module Full = On

module Rust = struct
  include On
  include Off.For_loop
  include Off.Monadic_action
  include Off.Monadic_binding
end

module FStar = struct
  include Off
  include On.Monadic_binding
  include On.Macro
end

module Coq = struct
  include On
end

module _ = struct
  module _ : T = Full
  module _ : T = Rust
  module _ : T = FStar
  module _ : T = Coq
end

module DefaultClasses (F : T) = struct
  open Base

  (* TODO: generate those classes automatically *)
  class virtual ['self] default_reduce_features =
    object (self : 'self)
      inherit [_] VisitorsRuntime.reduce

      (* todo: here I force unit to get rid of generalization issues
         Instead, TODO: split this class into multiple
      *)
      method visit_loop () (_ : F.loop) = self#zero
      method visit_for_loop () (_ : F.for_loop) = self#zero
      method visit_continue () (_ : F.continue) = self#zero
      method visit_mutable_variable () (_ : F.mutable_variable) = self#zero
      method visit_mutable_reference () (_ : F.mutable_reference) = self#zero
      method visit_mutable_pointer () (_ : F.mutable_pointer) = self#zero
      method visit_reference () (_ : F.reference) = self#zero
      method visit_slice () (_ : F.slice) = self#zero
      method visit_raw_pointer () (_ : F.raw_pointer) = self#zero
      method visit_early_exit () (_ : F.early_exit) = self#zero
      method visit_macro () (_ : F.macro) = self#zero
      method visit_as_pattern () (_ : F.as_pattern) = self#zero
      method visit_lifetime () (_ : F.lifetime) = self#zero
      method visit_monadic_action () (_ : F.monadic_action) = self#zero
      method visit_monadic_binding () (_ : F.monadic_binding) = self#zero
      method visit_arbitrary_lhs () (_ : F.arbitrary_lhs) = self#zero
    end

  class virtual ['self] default_map_features =
    object (self : 'self)
      inherit ['env] VisitorsRuntime.map

      (* todo: here I force unit to get rid of generalization issues
         Instead, TODO: split this class into multiple
      *)
      method visit_loop : 'env -> F.loop -> F.loop = Fn.const Fn.id
      method visit_continue : 'env -> F.continue -> F.continue = Fn.const Fn.id
      method visit_for_loop : 'env -> F.for_loop -> F.for_loop = Fn.const Fn.id

      method visit_mutable_variable
          : 'env -> F.mutable_variable -> F.mutable_variable =
        Fn.const Fn.id

      method visit_mutable_reference
          : 'env -> F.mutable_reference -> F.mutable_reference =
        Fn.const Fn.id

      method visit_mutable_pointer
          : 'env -> F.mutable_pointer -> F.mutable_pointer =
        Fn.const Fn.id

      method visit_reference : 'env -> F.reference -> F.reference =
        Fn.const Fn.id

      method visit_slice : 'env -> F.slice -> F.slice = Fn.const Fn.id

      method visit_raw_pointer : 'env -> F.raw_pointer -> F.raw_pointer =
        Fn.const Fn.id

      method visit_early_exit : 'env -> F.early_exit -> F.early_exit =
        Fn.const Fn.id

      method visit_macro : 'env -> F.macro -> F.macro = Fn.const Fn.id

      method visit_as_pattern : 'env -> F.as_pattern -> F.as_pattern =
        Fn.const Fn.id

      method visit_lifetime : 'env -> F.lifetime -> F.lifetime = Fn.const Fn.id

      method visit_arbitrary_lhs : 'env -> F.arbitrary_lhs -> F.arbitrary_lhs =
        Fn.const Fn.id

      method visit_monadic_action : 'env -> F.monadic_action -> F.monadic_action
          =
        Fn.const Fn.id

      method visit_monadic_binding
          : 'env -> F.monadic_binding -> F.monadic_binding =
        Fn.const Fn.id
    end
end

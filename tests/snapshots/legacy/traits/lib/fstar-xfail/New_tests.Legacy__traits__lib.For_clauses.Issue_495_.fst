module New_tests.Legacy__traits__lib.For_clauses.Issue_495_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): proverif(HAX0001)
let original_function_from_495_ (list: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : Prims.unit =
  let (e_indices: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Filter.t_Filter
          (Core_models.Ops.Range.t_Range u8) (u8 -> bool))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      (Core_models.Iter.Traits.Iterator.f_filter #(Core_models.Ops.Range.t_Range u8)
          #FStar.Tactics.Typeclasses.solve
          #(u8 -> bool)
          ({ Core_models.Ops.Range.f_start = mk_u8 0; Core_models.Ops.Range.f_end = mk_u8 5 }
            <:
            Core_models.Ops.Range.t_Range u8)
          (fun i ->
              let i:u8 = i in
              let (_: Core_models.Slice.Iter.t_Iter u8), (out: bool) =
                Core_models.Iter.Traits.Iterator.f_any #(Core_models.Slice.Iter.t_Iter u8)
                  #FStar.Tactics.Typeclasses.solve
                  #(u8 -> bool)
                  (Core_models.Slice.impl__iter #u8 (Alloc.Vec.impl_1__as_slice list <: t_Slice u8)
                    <:
                    Core_models.Slice.Iter.t_Iter u8)
                  (fun n ->
                      let n:u8 = n in
                      n =. i <: bool)
              in
              out)
        <:
        Core_models.Iter.Adapters.Filter.t_Filter (Core_models.Ops.Range.t_Range u8) (u8 -> bool))
  in
  ()

/// @fail(extraction): proverif(HAX0001)
let minimized_1_ (list: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Filter.t_Filter
        (Core_models.Ops.Range.t_Range u8) (u8 -> bool))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    (Core_models.Iter.Traits.Iterator.f_filter #(Core_models.Ops.Range.t_Range u8)
        #FStar.Tactics.Typeclasses.solve
        #(u8 -> bool)
        ({ Core_models.Ops.Range.f_start = mk_u8 0; Core_models.Ops.Range.f_end = mk_u8 5 }
          <:
          Core_models.Ops.Range.t_Range u8)
        (fun temp_0_ ->
            let _:u8 = temp_0_ in
            true)
      <:
      Core_models.Iter.Adapters.Filter.t_Filter (Core_models.Ops.Range.t_Range u8) (u8 -> bool))

let minimized_2_
      (it:
          Core_models.Iter.Adapters.Filter.t_Filter (Core_models.Ops.Range.t_Range u8) (u8 -> bool))
    : Prims.unit =
  let (e_indices: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core_models.Iter.Traits.Iterator.f_collect #(Core_models.Iter.Adapters.Filter.t_Filter
          (Core_models.Ops.Range.t_Range u8) (u8 -> bool))
      #FStar.Tactics.Typeclasses.solve
      #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      it
  in
  ()

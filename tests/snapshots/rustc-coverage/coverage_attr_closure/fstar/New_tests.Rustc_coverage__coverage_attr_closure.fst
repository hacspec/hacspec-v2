module New_tests.Rustc_coverage__coverage_attr_closure
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0001)
let v_GLOBAL_CLOSURE_ON:  string -> Prims.unit =
  fun input ->
    let input:string = input in
    let args:string = input <: string in
    let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
      let list = [Core_models.Fmt.Rt.impl__new_display #string args] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list
    in
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
            (mk_usize 1)
            (let list = [""; "\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list)
            args
          <:
          Core_models.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0001)
let v_GLOBAL_CLOSURE_OFF:  string -> Prims.unit =
  fun input ->
    let input:string = input in
    let args:string = input <: string in
    let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
      let list = [Core_models.Fmt.Rt.impl__new_display #string args] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list
    in
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
            (mk_usize 1)
            (let list = [""; "\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list)
            args
          <:
          Core_models.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0001, HAX0001)
let contains_closures_on (_: Prims.unit) : Prims.unit =
  let e_local_closure_on: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:string = input <: string in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_display #string args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  let e_local_closure_off: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:string = input <: string in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_display #string args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  ()

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0001, HAX0001)
let contains_closures_off (_: Prims.unit) : Prims.unit =
  let e_local_closure_on: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:string = input <: string in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_display #string args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  let e_local_closure_off: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:string = input <: string in
      let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core_models.Fmt.Rt.impl__new_display #string args] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core_models.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = contains_closures_on () in
  let _:Prims.unit = contains_closures_off () in
  ()

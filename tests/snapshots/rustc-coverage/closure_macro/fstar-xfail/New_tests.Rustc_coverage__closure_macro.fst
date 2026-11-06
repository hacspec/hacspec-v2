module New_tests.Rustc_coverage__closure_macro
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let load_configuration_files (_: Prims.unit)
    : Core_models.Result.t_Result Alloc.String.t_String Alloc.String.t_String =
  Core_models.Result.Result_Ok
  (Core_models.Convert.f_from #Alloc.String.t_String
      #string
      #FStar.Tactics.Typeclasses.solve
      "config")
  <:
  Core_models.Result.t_Result Alloc.String.t_String Alloc.String.t_String

/// @fail(extraction): ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0001)
let main (_: Prims.unit) : Core_models.Result.t_Result Prims.unit Alloc.String.t_String =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
          (let list = ["Starting service\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core_models.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  match
    Core_models.Result.impl__or_else #Alloc.String.t_String
      #Alloc.String.t_String
      #Alloc.String.t_String
      #(Alloc.String.t_String
          -> Core_models.Result.t_Result Alloc.String.t_String Alloc.String.t_String)
      (load_configuration_files ()
        <:
        Core_models.Result.t_Result Alloc.String.t_String Alloc.String.t_String)
      (fun e ->
          let e:Alloc.String.t_String = e in
          let args:Alloc.String.t_String = e <: Alloc.String.t_String in
          let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
            let list = [Core_models.Fmt.Rt.impl__new_display #Alloc.String.t_String args] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list
          in
          let message:Alloc.String.t_String =
            Core_models.Hint.must_use #Alloc.String.t_String
              (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                      (mk_usize 1)
                      (let list = ["Error loading configs: "] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                      args
                    <:
                    Core_models.Fmt.t_Arguments)
                <:
                Alloc.String.t_String)
          in
          if (Alloc.String.impl_String__len message <: usize) >. mk_usize 0
          then
            let args:Alloc.String.t_String = message <: Alloc.String.t_String in
            let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
              let list = [Core_models.Fmt.Rt.impl__new_display #Alloc.String.t_String args] in
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
            Core_models.Result.Result_Ok
            (Core_models.Convert.f_from #Alloc.String.t_String
                #string
                #FStar.Tactics.Typeclasses.solve
                "ok")
            <:
            Core_models.Result.t_Result Alloc.String.t_String Alloc.String.t_String
          else
            let _:Prims.unit =
              if (Core_models.Str.impl_str__len "error" <: usize) >. mk_usize 0
              then
                let _:Prims.unit =
                  Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["no msg\n"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core_models.Fmt.t_Arguments)
                in
                let _:Prims.unit = () in
                ()
              else
                let _:Prims.unit =
                  Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["error\n"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core_models.Fmt.t_Arguments)
                in
                let _:Prims.unit = () in
                ()
            in
            Core_models.Result.Result_Err
            (Core_models.Convert.f_from #Alloc.String.t_String
                #string
                #FStar.Tactics.Typeclasses.solve
                "error")
            <:
            Core_models.Result.t_Result Alloc.String.t_String Alloc.String.t_String)
    <:
    Core_models.Result.t_Result Alloc.String.t_String Alloc.String.t_String
  with
  | Core_models.Result.Result_Ok config ->
    let startup_delay_duration:Alloc.String.t_String =
      Core_models.Convert.f_from #Alloc.String.t_String
        #string
        #FStar.Tactics.Typeclasses.solve
        "arg"
    in
    let _:(Alloc.String.t_String & Alloc.String.t_String) =
      config, startup_delay_duration <: (Alloc.String.t_String & Alloc.String.t_String)
    in
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Alloc.String.t_String
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result Prims.unit Alloc.String.t_String

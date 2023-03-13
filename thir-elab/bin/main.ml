open Thir_elab.Raw_thir_ast
open Core
open Thir_elab.Utils
open Thir_elab
open Desugar_utils

let () =
  Fstar_backend.register;
  Coq_backend.register;
  Printexc.record_backtrace true;
  exit (Cmdliner.Cmd.eval (Backend.Registration.command ()))

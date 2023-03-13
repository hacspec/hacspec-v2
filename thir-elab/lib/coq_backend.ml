open Utils
open Base

module CoqBackend = struct
  let name = "coq"

  module InputLanguage = struct
    open Features
    include On
  end

  module RejectNotCoq (FA : Features.T) = struct
    module FB = InputLanguage

    include
      Feature_gate.Make (FA) (FB)
        (struct
          module A = FA
          module B = FB
          include Feature_gate.DefaultSubtype

          let mutable_variable = reject
          let loop = reject
          let continue = reject
          let mutable_reference = reject
          let mutable_pointer = reject
          let mutable_borrow = reject
          let reference = reject
          let slice = reject
          let raw_pointer = reject
          let early_exit _ = Obj.magic ()
          let macro _ = Features.On.macro
          let as_pattern = reject
          let lifetime = reject
          let monadic_action = reject
          let arbitrary_lhs = reject
          let monadic_binding _ = Features.On.monadic_binding
          let for_loop = reject
          let metadata = Desugar_utils.Metadata.make "RejectNotCoq"
        end)
  end

  module AST = Ast.Make (InputLanguage)

  module BackendOptions = struct
    open Cmdliner

    type t = ()

    let parse = Term.(const ())
  end

  open Ast
  module U = Ast_utils.Make (InputLanguage)
  open AST

  (* Helpers for constructing an Coq surface AST *)
  module C = struct
    (* module AST = FStar_Parser_AST (\* https://ocaml.org/p/fstar/2022.01.15/doc/FStar_Parser_AST/index.html *\) *)
    module AST = struct
      type int_size =
        | U8
        | U16
        | U32
        | U64
        | U128

      type ty =
        | Bool
        | Int of int_size * bool
        | Name of string
        | RecordTy of string * (string * ty) list

      type literal =
        | Const_string of string
        | Const_char of int
        | Const_int of string
        | Const_bool of bool

      type pat =
        | Wild
        | Ident of string
        | Lit of literal
        | RecordPat of string * (string * pat) list

      type term =
        | Let of pat * term * term
        | If of term * term * term
        | Match of term * (pat * term) list
        | Const of literal
        | Literal of string
        | App of term * term list
        | AppBin of string * term * term
        | Var of string
        | Name of string
        | RecordConstructor of term * term list

      type decl =
        | Unimplemented of string
        | Fn of string * term * ty
        | Notation of string * ty
        | Record of string * (string * ty) list
        | Inductive of string * (string * ty) list
    end
  end

  module Context = struct
    type t = { current_namespace : string * string list }
  end

  let tabsize = 2
  let newline_indent depth : string =
    "\n" ^ String.make (tabsize * depth) ' '

  let int_size_to_string (x : C.AST.int_size) : string =
    match x with
    | C.AST.U8 -> "WORDSIZE8"
    | C.AST.U16 -> "WORDSIZE16"
    | C.AST.U32 -> "WORDSIZE32"
    | C.AST.U64 -> "WORDSIZE64"
    | C.AST.U128 -> "WORDSIZE128"
    | _ -> .

  let rec ty_to_string (x : C.AST.ty) : string * string =
    match x with
    | C.AST.Bool -> "", "bool"
    | C.AST.Int (int_size, true) -> "", "@int" ^ " " ^ int_size_to_string int_size
    | C.AST.Int (int_size, false) -> "", "@int" ^ " " ^ int_size_to_string int_size
    | C.AST.Name s -> "", s
    | C.AST.RecordTy (name, fields) ->
       let (fields_def, fields_str) = record_fields_to_string fields in
       fields_def ^ "Record" ^ " " ^ name ^ " " ^ ":" ^ " " ^ "Type" ^ " " ^ ":=" ^ "{" ^ fields_str ^ newline_indent 0 ^ "}" ^ "." ^ newline_indent 0, name
    | _ -> .
  and record_fields_to_string (x : (string * C.AST.ty) list) : string * string =
    match x with
    | (name, ty) :: xs ->
       let ty_def, ty_str = ty_to_string ty in
       let xs_def, xs_str = record_fields_to_string xs in
       ty_def ^ xs_def, newline_indent 1 ^ name ^ ":" ^ ty_str ^ ";" ^ xs_str
    | _ -> "", ""

  let literal_to_string (x : C.AST.literal) : string =
    match x with
    | Const_string s -> s
    | Const_char c -> Int.to_string c (* TODO *)
    | Const_int i -> i
    | Const_bool b -> Bool.to_string b
    | _ -> .

  let rec pat_to_string (x : C.AST.pat) depth : string =
    match x with
    | C.AST.Wild -> "_"
    | C.AST.Ident s -> s
    | C.AST.Lit l ->
       literal_to_string l
    | C.AST.RecordPat (name, args) ->
       name ^ " " ^ "{|" ^ record_pat_to_string args (depth+1) ^ newline_indent depth
       ^ "|}"
    | _ -> .
  and record_pat_to_string args depth : string =
    match args with
    | (name, pat) :: xs ->
       newline_indent depth ^ name ^ ":=" ^ " " ^ pat_to_string pat depth ^ ";" ^ record_pat_to_string xs depth
    | _ -> ""

  let rec term_to_string (x : C.AST.term) depth : string =
    match x with
    | C.AST.Let (pat, bind, term) ->
       "let" ^ " " ^ pat_to_string pat depth ^ " " ^ ":=" ^ " " ^ term_to_string bind (depth+1) ^ " " ^ "in" ^ newline_indent depth
       ^ term_to_string term depth
    | C.AST.If (cond, then_, else_) ->
       "if" ^ newline_indent (depth+1)
       ^ term_to_string cond (depth+1) ^ newline_indent depth
       ^ "then"  ^ newline_indent (depth+1)
       ^ term_to_string then_ (depth+1) ^ newline_indent depth
       ^ "else" ^ newline_indent (depth+1)
       ^ term_to_string else_ (depth+1)
    | C.AST.Match (match_val, arms) ->
       "match" ^ " "  ^ term_to_string match_val (depth+1) ^ " " ^ "with" ^ newline_indent depth ^ arm_to_string arms depth ^ "end"
    | C.AST.Const c -> literal_to_string c
    | C.AST.Literal s -> s
    | C.AST.App (f, args) ->
       term_to_string f depth ^ args_to_string args depth
    | C.AST.AppBin (f, arga, argb) ->
       term_to_string arga depth ^ " " ^ f ^ " " ^ term_to_string argb depth
    | C.AST.Var s -> s
    | C.AST.Name s -> s
    | C.AST.RecordConstructor (f, args) ->
       term_to_string f depth ^ "{" ^ args_to_string args depth ^ "}"
    | _ -> .

  and args_to_string (args : C.AST.term list) depth : string =
    match args with
    | (x :: xs)  -> " " ^ term_to_string x depth ^ args_to_string xs depth
    | _ -> ""

  and arm_to_string (x : (C.AST.pat * C.AST.term) list) depth : string =
    match x with
    | ((pat, body) :: xs) ->
       "|" ^ " " ^ pat_to_string pat depth ^ " " ^ "=>" ^ " " ^ term_to_string body (depth+1) ^ newline_indent depth ^ arm_to_string xs depth
    | _ -> ""

  let rec decl_to_string (x : C.AST.decl) : string =
    match x with
    | C.AST.Unimplemented s -> "(*" ^ s ^ "*)"
    | C.AST.Fn (name, term, ty) ->
       let (definitions, ty_str) = ty_to_string ty in
       definitions ^ "Definition" ^ " " ^ name ^ " " ^ ":" ^ " " ^ ty_str ^ " " ^ ":=" ^ newline_indent 1 ^ term_to_string term 1 ^ "."
    | C.AST.Notation (name, ty) ->
       let (definitions, ty_str) = ty_to_string ty in
       definitions ^ "Notation" ^ " " ^ name ^ " " ^ ":=" ^ " " ^ ty_str ^ "."
    | C.AST.Record (name, variants) ->
       let (definitions, variants_str) = variants_to_string variants (newline_indent 1) ";" in
       definitions ^ "Record" ^ " " ^ name ^ " " ^ ":" ^ " " ^ "Type" ^ " " ^ ":=" ^ "{" ^ variants_str ^ newline_indent 0 ^ "}."
    | C.AST.Inductive (name, variants) ->
       let (definitions, variants_str) = variants_to_string variants (newline_indent 0 ^ "|" ^ " ") (" " ^ "->" ^ " " ^ name) in
       definitions ^ "Inductive" ^ " " ^ name ^ " " ^ ":" ^ " " ^ "Type" ^ " " ^ ":=" ^ variants_str ^ "."
    | _ -> .
  and variants_to_string variants pre post : string * string =
    match variants with
    | (ty_name, ty) :: xs ->
       let (ty_definitions, ty_str) = ty_to_string ty in
       let (variant_definitions, variants_str) = variants_to_string xs pre post in
       ty_definitions ^ variant_definitions , pre ^ ty_name ^ " " ^ ":" ^ " " ^ ty_str ^ post ^ variants_str
    | _ -> "", ""

  let rec path_to_string (l : string list) : string =
    match l with
    | [x] -> x
    | x :: xs -> x ^ "_" ^ (path_to_string xs)
    | _ -> ""

  let rec path_to_string_last (l : string list) : string =
    match l with
    | [x] -> x
    | x :: xs -> (path_to_string xs)
    | _ -> ""

  (* let rec pglobal_ident (id : global_ident) = *)
  (*   match id with *)
  (*   | `Concrete cid -> F.lid (cid.crate :: Non_empty_list.to_list cid.path) *)
  (*   | `Primitive prim_id -> pprim_ident prim_id *)
  (*   | `TupleType 0 -> F.lid [ "prims"; "unit" ] *)
  (*   | `TupleCons n when n <= 1 -> *)
  (*       failwith ("Got a [TupleCons " ^ string_of_int n ^ "]") *)
  (*   | `TupleType n when n <= 14 -> *)
  (*       F.lid [ "FStar"; "Pervasives"; "tuple" ^ string_of_int n ] *)
  (*   | `TupleCons n when n <= 14 -> *)
  (*       F.lid [ "FStar"; "Pervasives"; "Mktuple" ^ string_of_int n ] *)
  (*   | `TupleType _ | `TupleCons _ -> *)
  (*       failwith "F* doesn't support tuple of size greater than 14" *)
  (*   | `TupleField _ | `Projector _ -> *)
  (*       failwith ("Cannot appear here: " ^ show_global_ident id) *)

  let primitive_to_string (id : primitive_ident) : string =
    match id with
    | Box -> failwith "Box"
    | Deref -> failwith "Box"
    | Cast -> failwith "Cast"
    | BinOp op ->
       (
         match op with
         | Add -> "int_add"
         | Sub -> "int_sub"
         | Mul -> "int_mul"
         | Div -> "int_div"
         | Eq -> "eq_op"
         | Lt -> "lt_op"
         | Le -> "le_op"
         | Ge -> "ge_op"
         | Gt -> "gt_op"
         | Ne -> "ne_op"
         | Rem -> failwith "TODO: Rem"
         | BitXor -> failwith "TODO: BitXor"
         | BitAnd -> failwith "TODO: BitAnd"
         | BitOr -> failwith "TODO: BitOr"
         | Shl -> failwith "TODO: Shl"
         | Shr -> failwith "TODO: Shr"
         | Offset -> failwith "TODO: Offset")
    | UnOp op ->
       "UnOp"
    (* ( *)
    (* match op with *)
    (* | Not -> F.lid [ "Prims"; "l_Not" ] *)
    (* | Neg -> F.lid [ "Prims"; "op_Minus" ]) *)
    | LogicalOp op ->
       "LogicOp"
  (* ( *)
  (*  match op with *)
  (*  | And -> F.lid [ "Prims"; "op_AmpAmp" ] *)
  (*  | Or -> F.lid [ "Prims"; "op_BarBar" ]) *)


  let global_ident_to_string (id : global_ident) : string =
    match id with
    | `Concrete { crate; path } ->
       (* crate ^ "_" ^ *) (path_to_string (Non_empty_list.to_list path))
    | `Primitive p_id -> primitive_to_string p_id
    | _ -> "name of fn"
  (* | `TupleType of int *)
  (* | `TupleCons of int *)
  (* | `TupleField of int * int *)
  (* | `Projector of [ `Concrete of concrete_ident | `TupleField of int * int ] *)
  (* ] *)

  let global_ident_to_string_last (id : global_ident) : string =
    match id with
    | `Concrete { crate; path } ->
       path_to_string_last (Non_empty_list.to_list path)
    | _ -> "name of fn"

  module Make (Ctx : sig
    val ctx : Context.t
  end) =
  struct
    open Ctx

    let __TODO_pat__ s = C.AST.Ident (s ^ " todo(pat)")

    let rec pliteral (e : literal) =
      match e with
      | String s -> C.AST.Const_string s
      | Char c -> C.AST.Const_char (Char.to_int c)
      | Int { value } -> C.AST.Const_int (Bigint.to_string value)
      | Float _ -> failwith "Float: todo"
      | Bool b -> C.AST.Const_bool b

    let rec ppat (p : pat) : C.AST.pat =
      match p.p with
      | PWild -> C.AST.Wild
      | PAscription { typ; pat } -> __TODO_pat__ "ascription"
      | PBinding { mut = Immutable; mode = _; subpat = None; var; typ = _ (* we skip type annot here *); } ->
         C.AST.Ident (var.name)
      | PArray { args } -> __TODO_pat__ "array"
      | PConstruct { name = `TupleCons 0; args = [] } -> __TODO_pat__ "tuple 0"
      | PConstruct { name = `TupleCons 1; args = [ { pat } ] } -> __TODO_pat__ "tuple 1"
      | PConstruct { name = `TupleCons n; args } -> __TODO_pat__ "tuple n"
      | PConstruct { name; args; record } ->
         C.AST.RecordPat (global_ident_to_string_last name, pfield_pats args)
      | PConstant { lit } ->
         C.AST.Lit (pliteral lit)
      | PDeref { subpat } -> __TODO_pat__ "deref"
      | _ -> __TODO_pat__ "should never happen"
    and pfield_pats (args : field_pat list) : (string * C.AST.pat) list =
      match args with
      | { field; pat } :: xs ->
         (global_ident_to_string_last field, ppat pat) :: pfield_pats xs
      | _ -> []

    let op_to_string (op : Ast.bin_op) =
      match op with
      | Add -> "+"
      | Sub -> "-"
      | Mul -> "*"
      | Div -> "/"
      | Eq -> "="
      | Lt -> "<"
      | Le -> "<="
      | Ge -> ">="
      | Gt -> ">"
      | Ne -> "<>"
      | Rem -> failwith "TODO: Rem"
      | BitXor -> failwith "TODO: BitXor"
      | BitAnd -> failwith "TODO: BitAnd"
      | BitOr -> failwith "TODO: BitOr"
      | Shl -> failwith "TODO: Shl"
      | Shr -> failwith "TODO: Shr"
      | Offset -> failwith "TODO: Offset"

    let __TODO_term__ s = C.AST.Const (C.AST.Const_string (s ^ " todo(term)"))

    let rec pexpr (e : expr) : C.AST.term =
      match e.e with
      | Literal e ->
         C.AST.Const (pliteral e)
      | LocalVar local_ident -> C.AST.Name local_ident.name
      | GlobalVar (`TupleCons 0)
        | Construct { constructor = `TupleCons 0; fields = [] } ->
         __TODO_term__ "global var 0 / construct 0"
      | GlobalVar global_ident ->
         C.AST.Var (global_ident_to_string global_ident)
      | App { f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
              args = [ arg ]; } ->
         __TODO_term__ "app global vcar projector tuple"
      | App { f = { e = GlobalVar (`Primitive (BinOp op)) }; args = [ arga; argb ]; } ->
         C.AST.AppBin (op_to_string op, pexpr arga, pexpr argb)
      | App { f; args } ->
         let base = pexpr f in
         let args = List.map ~f:pexpr args in
         C.AST.App (base, args)
      | If { cond; then_; else_ } ->
         C.AST.If (pexpr cond, pexpr then_, Option.value_map else_ ~default:(C.AST.Literal "()") ~f:pexpr)
      | Array l ->
         __TODO_term__ "array"
      | Let { lhs; rhs; body; monadic = Some monad } ->
         C.AST.Let (ppat lhs, pexpr rhs, pexpr body)
      | Let { lhs; rhs; body; monadic = None } ->
         C.AST.Let (ppat lhs, pexpr rhs, pexpr body)
      | MonadicAction _ -> __TODO_term__ "monadic action"
      | Match { scrutinee; arms } ->
         C.AST.Match (pexpr scrutinee, List.map ~f:(fun { arm = { pat; body } } -> (ppat pat, pexpr body)) arms)
      | Ascription { e; typ } ->
         __TODO_term__ "asciption"
      | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
         __TODO_term__ "construct tuplecons 1"
      | Construct { constructor = `TupleCons n; fields; base } ->
         __TODO_term__ "construct tuplecons n"
      | Construct { constructs_record = true; constructor; fields; base } ->
         __TODO_term__ "record true"
      | Construct { constructs_record = false; constructor; fields; base } ->
         C.AST.RecordConstructor (C.AST.Var (global_ident_to_string constructor), [__TODO_term__ "args"])
      | Closure { params; body } -> __TODO_term__ "closure"
      | Return { e } -> __TODO_term__ "return"
      (* Macro *)
      | MacroInvokation {
macro;
args;
witness;
} ->
         __TODO_term__ "macro"
      (* Mut *)
      | Assign { lhs; e; witness } ->
         __TODO_term__ "assign"
      (* Loop *)
      | Loop { body; label; witness } ->
         __TODO_term__ "loop"
      (* ControlFlow *)
      | Break { e; label; witness } -> __TODO_term__ "break"
      | Continue { label; witness } -> __TODO_term__ "continue"
      (* Mem *)
      | Borrow { kind; e; witness } -> __TODO_term__ "borrow"
      (* Raw borrow *)
      | AddressOf { mut;
                    e;
                    witness; } -> __TODO_term__ "raw borrow"
      | Literal l -> __TODO_term__ "literal"
      | ForLoop { start;
                  end_;
                  var;
                  body;
                  label;
                  witness; } -> __TODO_term__ "for loop"
      | _ -> .

    let __TODO_ty__ s : C.AST.ty = C.AST.Name (s ^ " todo(ty)")

    let rec pty (t : ty) : C.AST.ty =
      match t with
      | TBool -> C.AST.Bool
      | TChar -> __TODO_ty__ "char"
      | TInt k -> C.AST.Int ((match k.size with
                              | S8 -> U8
                              | S16 -> U16
                              | S32 -> U32
                              | S64 -> U64
                              | S128 -> U128
                              | SSize -> U32), k.signedness == Signed)
      | TStr -> __TODO_ty__ "str"
      | TFalse -> __TODO_ty__ "false"
      | TApp { ident = `TupleType 0 as ident; args = [] } ->
         __TODO_ty__ "app 0"
      | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty ty
      | TApp { ident = `TupleType n; args } when n >= 2 ->
         __TODO_ty__ "app >= 2"
      | TApp { ident; args } ->
         __TODO_ty__ "app"
      | TArrow (inputs, output) ->
         __TODO_ty__ "arrow"
      | TFloat -> failwith "pty: Float"
      | TArray { typ; length } ->
         __TODO_ty__ "array"
      | TParam i ->
         __TODO_ty__ "param"
      | TProjectedAssociatedType s -> failwith "proj:assoc:type"
      | _ -> __TODO_ty__ "other??"

    let __TODO_item__ s = C.AST.Unimplemented (s ^ " todo(item)")

    let rec pitem (e : item) : C.AST.decl list =
      [ match e.v with
        | Fn { name; generics; body; params } ->
           C.AST.Fn (global_ident_to_string name, pexpr body, pty body.typ)
        | TyAlias { name; generics; ty } ->
           C.AST.Notation (global_ident_to_string name, pty ty)
        (* record *)
        | Type { name; generics; variants = [{name=record_name; arguments}]; record = true } ->
           C.AST.Record (global_ident_to_string_last name, p_record_record arguments)
        (* enum *)
        | Type { name; generics; variants; record = true } ->
           C.AST.Inductive (global_ident_to_string_last name, p_record variants name)
        | Type { name; generics; variants } ->
           __TODO_item__ "Type not record"
        | NotImplementedYet -> __TODO_item__ "Not implemented yet?"
        | _ ->
           __TODO_item__ "Definition?" ]

    (* | Enum (variants, generics) -> *)
    (*    let name = def_id (Option.value_exn item.def_id) in *)
    (*    let generics = c_generics generics in *)
    (*    let variants = *)
    (*      List.map *)
    (*        ~f:(fun { ident; data; def_id = variant_id } -> *)
    (*          match data with *)
    (*          | Tuple (fields, _, _) | Struct (fields, _) -> *)
    (*             let arguments = *)
    (*               List.map *)
    (*                 ~f:(fun { def_id = id; ty } -> (def_id id, c_ty ty)) *)
    (*                 fields *)
    (*             in *)
    (*             { name = def_id variant_id; arguments } *)
    (*          | Unit (_, name) -> { name = def_id name; arguments = [] }) *)
    (*        variants *)
    (*    in *)
    (*    Type { name; generics; variants; record = true } *)
    (* | Struct (v, generics) -> *)
    (*    let name = def_id (Option.value_exn item.def_id) in *)
    (*    let generics = c_generics generics in *)
    (*    let v, record = *)
    (*      let mk fields = *)
    (*        let arguments = *)
    (*          List.map *)
    (*            ~f:(fun Thir.{ def_id = id; ty } -> (def_id id, c_ty ty)) *)
    (*            fields *)
    (*        in *)
    (*        { name; arguments } *)
    (*      in *)
    (*      match v with *)
    (*      | Tuple (fields, _, _) -> (mk fields, false) *)
    (*      | Struct (fields, _) -> (mk fields, true) *)
    (*      | Unit (_, _) -> ({ name; arguments = [] }, false) *)
    (*    in *)
    (*    let variants = [ v ] in *)
    (*    Type { name; generics; variants; record } *)

    and p_record variants parrent_name : (string * C.AST.ty) list =
      match variants with
      | {name; arguments} :: xs
        ->
         (p_record_args arguments name) :: p_record xs parrent_name
      | _ -> []
    and p_record_args arguments name : (string * C.AST.ty) =
      match arguments with
      | [(arg_name, arg_ty)] -> (global_ident_to_string_last arg_name, pty arg_ty)
      | [] -> ("_", C.AST.Name "Missing values?")
      | _ -> (global_ident_to_string_last name, C.AST.RecordTy (global_ident_to_string name, p_record_record arguments))
    and p_record_record arguments : (string * C.AST.ty) list =
      match arguments with
      | (arg_name, arg_ty) :: xs -> (global_ident_to_string_last arg_name, pty arg_ty) :: p_record_record xs
      | _ -> []
  end

  module type S = sig
    val pitem : item -> C.AST.decl list
  end

  let make ctx =
    (module Make (struct
      let ctx = ctx
    end) : S)

  let string_of_item (item : item) : string =
    let (module Print) = make { current_namespace = item.parent_namespace } in
    List.map ~f:decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n"

  let string_of_items =
    List.map ~f:string_of_item >> List.map ~f:String.strip
    >> List.filter ~f:(String.is_empty >> not)
    >> String.concat ~sep:"\n\n"

  let hardcoded_coq_headers =
    "\n\
     Require Import MachineIntegers.\n
     Require Import Hacspec_Lib."

  (* module AST : Ast.T *)

  let modules_to_string (o : Backend.Options.t) modules =
    let out_dir = "out/" in
    (try Caml.Sys.mkdir out_dir 0o777 with Sys_error _ -> ());
    List.iter
      ~f:(fun (relative_path, data) ->
        if not (String.equal relative_path "Hacspec_lib.fst") then (
          let file = out_dir ^ relative_path in
          Core.Out_channel.write_all file ~data;
          print_endline @@ "Wrote " ^ file))
      modules

  let translate (o : Backend.Options.t) (bo : BackendOptions.t)
      (items : AST.item list) : unit =
    U.group_items_by_namespace items
    |> Map.to_alist
    |> List.map ~f:(fun (ns, items) ->
           let mod_name =
             String.concat ~sep:"."
               (List.map
                  ~f:(map_first_letter String.uppercase)
                  (fst ns :: snd ns))
           in
           ( mod_name ^ ".fst",
             "module " ^ mod_name ^ hardcoded_coq_headers ^ "\n\n"
             ^ string_of_items items ))
    |> modules_to_string o

  open Desugar_utils

  module DesugarToInputLanguage =
    [%functor_application
       Reject.RawOrMutPointer(Features.Rust)
    |> Reject.Arbitrary_lhs
    |> Resugar_for_loop.Make
    |> Desugar_direct_and_mut.Make
    |> Reject.Continue
    |> Desugar_drop_references.Make
    |> (fun X ->
        (Desugar_mutable_variable.Make(module X))
          (module struct
            let early_exit = fun _ -> Features.On.early_exit
          end))
    |> RejectNotCoq
    |> Identity
    ]
    [@ocamlformat "disable"]

  let desugar (o : Backend.Options.t) (bo : BackendOptions.t)
      (i : Ast.Rust.item) : AST.item list =
    DesugarToInputLanguage.ditem i
end

let register = Backend.Registration.register (module CoqBackend)

(* Untrusted artifact generator. Rocq independently checks the emitted AST.
   The pa source is compiled with the same resolved declarations. *)
open Tinyprover_core
module Source = Tinyprover_tp.Source

let rec term = function
  | Term.Type -> "tType" | Term.Kind -> "tKind"
  | Term.Var n -> Printf.sprintf "(tVar %d)" n
  | Term.Const n -> Printf.sprintf "(tConst %d)" n
  | Term.Pi (a,b) -> Printf.sprintf "(tPi %s %s)" (term a) (term b)
  | Term.Lam (a,b) -> Printf.sprintf "(tLam %s %s)" (term a) (term b)
  | Term.App (a,b) -> Printf.sprintf "(tApp %s %s)" (term a) (term b)

let write path contents =
  let c = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out_noerr c) (fun () -> output_string c contents)

let () =
  if Array.length Sys.argv <> 4 then failwith "usage: export PRELUDE.tp BASIC.tp OUTPUT_DIR";
  let prelude = Source.compile_file Sys.argv.(1) in
  let full = Source.compile_file Sys.argv.(2) in
  let count = List.length prelude.declarations in
  let prefix = List.filteri (fun i _ -> i < count) full.declarations in
  if prefix <> prelude.declarations then failwith "prelude is not an exact declaration prefix";
  let body = List.filteri (fun i _ -> i >= count) full.declarations in
  if List.exists (fun (d:Source.declaration) -> d.body = None) body then
    failwith "proof file introduces an axiom";
  let globals = ref [] in
  let encoded = List.mapi (fun i (d:Source.declaration) ->
    let a = Source.resolve !globals d.at d.typ in
    let result = match d.body with
      | None -> "Assume " ^ term a
      | Some b -> "Prove " ^ term a ^ " " ^ term (Source.resolve !globals d.at b)
    in
    globals := (d.name,i) :: !globals; result) full.declarations in
  let list xs = "[\n  " ^ String.concat ";\n  " xs ^ "\n]" in
  let before = List.filteri (fun i _ -> i < count) encoded in
  let after = List.filteri (fun i _ -> i >= count) encoded in
  let out name data = write (Filename.concat Sys.argv.(3) name) data in
  out "prelude.pa" prelude.assembly;
  let offset = String.length prelude.assembly in
  if String.sub full.assembly 0 offset <> prelude.assembly then failwith "assembly prefix mismatch";
  out "proofs.pa" (String.sub full.assembly offset (String.length full.assembly - offset));
  out "names.txt" (String.concat "\n" full.names ^ "\n");
  out "Artifact.v" ("From Stdlib Require Import List.\nFrom Rocq4pa Require Import Syntax Program.\nImport ListNotations.\n"
    ^ "Definition prelude : list declaration := " ^ list before ^ ".\n"
    ^ "Definition proofs : list declaration := " ^ list after ^ ".\n");
  Printf.printf "exported %d prelude declarations and %d proved declarations\n" count (List.length body)

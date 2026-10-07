From Stdlib Require Import Extraction ExtrOcamlBasic.
From Rocq4pa Require Import Syntax Kernel Program Checker.

(** Keep inductive naturals: no unchecked machine-integer arithmetic in
    the extracted kernel. Only the CLI converts bounded input indices. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "checker.ml" check_program.

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Tinyprover.Pa Require Import Syntax Kernel Program Checker Codec.

(** Keep inductive naturals: no unchecked machine-integer arithmetic in
    the extracted kernel. Only the CLI converts bounded input indices. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "checker.ml" check_program decode_pa.

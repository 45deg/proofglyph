From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Rocq4tp Require Import Compile PaCodec PaCompile.

(** Keep inductive naturals, as in rocq4pa. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "frontend.ml" compile lower encode_pa decode_pa compile_pa check_pa.

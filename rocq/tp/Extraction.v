From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Tinyprover.Tp Require Import Compile PaCodec PaCompile Desugar SurfaceCompile TpSyntax TpImports.

(** Keep inductive naturals, as in rocq4pa. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "frontend.ml" compile lower encode_pa decode_pa compile_pa check_pa
  desugar desugar_program compile_surface compile_surface_pa lex_tp parse_tp load_tp.

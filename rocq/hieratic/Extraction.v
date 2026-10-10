From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatBigInt.
From Proofglyph.Hieratic Require Import Compile ProofglyphCodec ProofglyphCompile Desugar SurfaceCompile HieraticSyntax HieraticImports FileCompile Elaboration.

(** Extract naturals to Zarith to avoid unary allocation and machine overflow.
    The standard extraction mappings and Zarith arithmetic are trusted. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "frontend.ml" compile lower encode_proofglyph decode_proofglyph compile_proofglyph check_proofglyph
  desugar desugar_program compile_surface compile_surface_proofglyph lex_hieratic parse_hieratic load_hieratic prepare_files compile_files compile_files_proofglyph compile_elaborated compile_files_elaborated compile_files_elaborated_proofglyph.

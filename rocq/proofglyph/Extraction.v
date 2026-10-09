From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatBigInt.
From Proofglyph.Language Require Import Syntax Kernel Program Checker Codec.

(** Extract naturals to Zarith to avoid unary allocation and machine overflow.
    The standard extraction mappings and Zarith arithmetic are trusted. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "checker.ml" check_program decode_proofglyph.

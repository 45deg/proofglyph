From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatBigInt.
From Proofglyph.Language Require Import Syntax Kernel Program CachedChecker Codec CacheExtraction.

(** Extract naturals to Zarith to avoid unary allocation and machine overflow.
    The standard extraction mappings and Zarith arithmetic are trusted. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "checker.ml" check_program decode_proofglyph.

(** Uncached reference used only by the runtime refinement tests. *)
Extraction "cache_reference.ml" WeakCheckerImpl.infer.

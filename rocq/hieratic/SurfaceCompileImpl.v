From Stdlib Require Import List String.
Import ListNotations.
From Tinyprover.Hieratic Require Export DesugarImpl ProofglyphCompileImpl.

Definition compile_surface fuel allow raw := compile fuel allow (desugar_program raw).
Definition compile_surface_proofglyph fuel allow raw := compile_proofglyph fuel allow (desugar_program raw).


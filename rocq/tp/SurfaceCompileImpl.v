From Stdlib Require Import List String.
Import ListNotations.
From Tinyprover.Tp Require Export DesugarImpl PaCompileImpl.

Definition compile_surface fuel allow raw := compile fuel allow (desugar_program raw).
Definition compile_surface_pa fuel allow raw := compile_pa fuel allow (desugar_program raw).


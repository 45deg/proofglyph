From Stdlib Require Import List String.
From Tinyprover.Pa Require Import Syntax Program WellFormed.
From Tinyprover.Tp Require Import Surface Desugar Compile PaCodec PaCompile.
Import ListNotations.

From Tinyprover.Tp Require Export SurfaceCompileImpl.

Theorem compile_surface_pa_sound fuel allow raw bytes sg :
  compile_surface_pa fuel allow raw = Some (bytes, sg) ->
  exists src ds, expands_program raw src /\
    bytes = encode_pa ds /\ decode_pa bytes = Some ds /\
    translates [] src ds /\ source_permitted allow src /\
    valid_program [] ds sg /\ wf_signature sg.
Proof.
  intros H; apply compile_pa_sound in H; destruct H as [ds H].
  exists (desugar_program raw), ds; split; [apply desugar_program_correct; reflexivity|exact H].
Qed.

Theorem compile_surface_pa_complete allow raw src ds sg :
  expands_program raw src -> translates [] src ds ->
  source_permitted allow src -> valid_program [] ds sg ->
  exists bound, forall fuel, bound <= fuel ->
    compile_surface_pa fuel allow raw = Some (encode_pa ds, sg).
Proof.
  intros E T P V; apply desugar_program_correct in E.
  unfold compile_surface_pa; rewrite E; apply compile_pa_complete; assumption.
Qed.

Theorem compile_surface_pa_recheck fuel allow raw bytes sg :
  compile_surface_pa fuel allow raw = Some (bytes, sg) -> check_pa fuel allow bytes = Some sg.
Proof. apply compile_pa_recheck. Qed.

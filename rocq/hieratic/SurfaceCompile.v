From Stdlib Require Import List String.
From Proofglyph.Language Require Import Syntax Program WellFormed.
From Proofglyph.Hieratic Require Import Surface Desugar Compile ProofglyphCodec ProofglyphCompile.
Import ListNotations.

From Proofglyph.Hieratic Require Export SurfaceCompileImpl.

Theorem compile_surface_proofglyph_sound fuel allow raw bytes sg :
  compile_surface_proofglyph fuel allow raw = Some (bytes, sg) ->
  exists src ds, expands_program raw src /\
    bytes = encode_proofglyph ds /\ decode_proofglyph bytes = Some ds /\
    translates [] src ds /\ source_permitted allow src /\
    valid_program [] ds sg /\ wf_signature sg.
Proof.
  intros H; apply compile_proofglyph_sound in H; destruct H as [ds H].
  exists (desugar_program raw), ds; split; [apply desugar_program_correct; reflexivity|exact H].
Qed.

Theorem compile_surface_proofglyph_complete allow raw src ds sg :
  expands_program raw src -> translates [] src ds ->
  source_permitted allow src -> valid_program [] ds sg ->
  exists bound, forall fuel, bound <= fuel ->
    compile_surface_proofglyph fuel allow raw = Some (encode_proofglyph ds, sg).
Proof.
  intros E T P V; apply desugar_program_correct in E.
  unfold compile_surface_proofglyph; rewrite E; apply compile_proofglyph_complete; assumption.
Qed.

Theorem compile_surface_proofglyph_recheck fuel allow raw bytes sg :
  compile_surface_proofglyph fuel allow raw = Some (bytes, sg) -> check_proofglyph fuel allow bytes = Some sg.
Proof. apply compile_proofglyph_recheck. Qed.

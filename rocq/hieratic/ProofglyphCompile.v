From Stdlib Require Import List String.
From Proofglyph.Language Require Import Syntax Program WellFormed CachedChecker.
From Proofglyph.Hieratic Require Import Surface Compile ProofglyphCodec.
Import ListNotations.

From Proofglyph.Hieratic Require Export ProofglyphCompileImpl.

Theorem compile_proofglyph_sound fuel allow src bytes sg :
  compile_proofglyph fuel allow src = Some (bytes, sg) ->
  exists ds, bytes = encode_proofglyph ds /\ decode_proofglyph bytes = Some ds /\
    translates [] src ds /\ source_permitted allow src /\
    valid_program [] ds sg /\ wf_signature sg.
Proof.
  unfold compile_proofglyph; destruct (compile fuel allow src) as [[ds final]|] eqn:C;
    intros H; inversion H; subst.
  destruct (compile_sound _ _ _ _ _ C) as [T [V [P W]]].
  exists ds; split; [reflexivity|]; split; [apply proofglyph_roundtrip|].
  split; [exact T|]; split.
  - apply (proj2 (translates_policy _ _ _ _ T)); exact P.
  - auto.
Qed.

Theorem compile_proofglyph_complete allow src ds sg :
  translates [] src ds -> source_permitted allow src -> valid_program [] ds sg ->
  exists bound, forall fuel, bound <= fuel ->
    compile_proofglyph fuel allow src = Some (encode_proofglyph ds, sg).
Proof.
  intros T P V; apply (proj1 (translates_policy _ _ _ _ T)) in P.
  destruct (compile_complete _ _ _ _ T P V) as [bound B].
  exists bound; intros fuel LE; unfold compile_proofglyph; rewrite (B fuel LE); reflexivity.
Qed.

Theorem compile_proofglyph_recheck fuel allow src bytes sg :
  compile_proofglyph fuel allow src = Some (bytes, sg) -> check_proofglyph fuel allow bytes = Some sg.
Proof.
  unfold compile_proofglyph, compile; destruct (lower [] src) as [ds|] eqn:L; [|discriminate].
  destruct (check_program fuel allow [] ds) eqn:C; intros H; inversion H; subst.
  unfold check_proofglyph; rewrite proofglyph_roundtrip; exact C.
Qed.

Theorem check_proofglyph_sound fuel allow bytes sg : check_proofglyph fuel allow bytes = Some sg ->
  exists ds, decode_proofglyph bytes = Some ds /\ permitted_declarations allow ds /\
    valid_program [] ds sg /\ wf_signature sg.
Proof.
  unfold check_proofglyph; destruct (decode_proofglyph bytes) as [ds|] eqn:D; [|discriminate].
  intros C; assert (W : wf_signature []) by constructor.
  destruct (proj1 (program_correct allow [] ds sg W) (ex_intro _ fuel C)) as [P V].
  exists ds; split; [reflexivity|]; split; [exact P|]; split; [exact V|].
  eapply accepted_program_wf; eauto.
Qed.

Theorem compile_proofglyph_monotone n m allow src bytes sg : n <= m ->
  compile_proofglyph n allow src = Some (bytes, sg) -> compile_proofglyph m allow src = Some (bytes, sg).
Proof.
  intros LE; unfold compile_proofglyph; destruct (compile n allow src) as [[ds final]|] eqn:C;
    intros H; inversion H; subst.
  rewrite (compile_monotone _ _ _ _ _ _ LE C); reflexivity.
Qed.

From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Proofglyph.Language Require Import Checker.
From Proofglyph.Hieratic Require Export CompileImpl.
From Proofglyph.Hieratic Require Import Resolve.

Lemma lower_decl_sound gs d d' : lower_decl gs d = Some d' -> translates_decl gs d d'.
Proof.
  destruct d as [n a [b|]]; unfold lower_decl; cbn.
  - destruct (resolve gs [] a) eqn:A; [|discriminate].
    destruct (resolve gs [] b) eqn:B; cbn; intros H; inversion H; subst.
    constructor; apply resolve_sound; assumption.
  - destruct (resolve gs [] a) eqn:A; intros H; inversion H; subst.
    constructor; apply resolve_sound; assumption.
Qed.

Lemma lower_decl_complete gs d d' : translates_decl gs d d' -> lower_decl gs d = Some d'.
Proof.
  intros H; destruct H; unfold lower_decl; cbn;
    rewrite (resolve_complete _ _ _ _ H); try rewrite (resolve_complete _ _ _ _ H0); reflexivity.
Qed.

Theorem lower_sound gs src ds : lower gs src = Some ds -> translates gs src ds.
Proof.
  revert gs ds; induction src as [|d rest IH]; intros gs ds H; cbn in H.
  - inversion H; constructor.
  - destruct (in_dec string_dec (decl_name d) gs); [discriminate|].
    destruct (lower_decl gs d) eqn:D; [|discriminate].
    destruct (lower (gs ++ [decl_name d]) rest) eqn:R; inversion H; subst.
    constructor; auto using lower_decl_sound.
Qed.

Theorem lower_complete gs src ds : translates gs src ds -> lower gs src = Some ds.
Proof.
  intros H; induction H; cbn; [reflexivity|].
  destruct (in_dec string_dec (decl_name d) gs); [contradiction|].
  rewrite (lower_decl_complete _ _ _ H0), IHtranslates; reflexivity.
Qed.

Theorem lower_correct gs src ds : lower gs src = Some ds <-> translates gs src ds.
Proof. split; [apply lower_sound|apply lower_complete]. Qed.

Theorem compile_sound fuel allow src ds sg : compile fuel allow src = Some (ds, sg) ->
  translates [] src ds /\ valid_program [] ds sg /\
  permitted_declarations allow ds /\ wf_signature sg.
Proof.
  unfold compile; destruct (lower [] src) eqn:L; [|discriminate].
  destruct (check_program fuel allow [] l) eqn:C; intros H; inversion H; subst.
  assert (W : wf_signature []) by constructor.
  destruct (proj1 (program_correct allow [] ds sg W) (ex_intro _ fuel C)) as [P V].
  split; [apply lower_sound; exact L|].
  split; [exact V|].
  split; [exact P|].
  eapply valid_program_preserves_wf; eauto.
Qed.

Theorem compile_complete allow src ds sg :
  translates [] src ds -> permitted_declarations allow ds -> valid_program [] ds sg ->
  exists bound, forall fuel, bound <= fuel -> compile fuel allow src = Some (ds, sg).
Proof.
  intros T P V.
  destruct (empty_signature_program_complete _ _ _ P V) as [bound B].
  exists bound; intros fuel LE; unfold compile.
  rewrite (lower_complete _ _ _ T), (B fuel LE); reflexivity.
Qed.

Theorem compile_monotone n m allow src ds sg : n <= m ->
  compile n allow src = Some (ds, sg) -> compile m allow src = Some (ds, sg).
Proof.
  intros LE; unfold compile; destruct (lower [] src); [|discriminate].
  destruct (check_program n allow [] l) eqn:C; intros H; inversion H; subst.
  rewrite (program_monotone _ _ _ _ _ _ LE C); reflexivity.
Qed.

Theorem compile_correct allow src ds sg :
  (exists fuel, compile fuel allow src = Some (ds, sg)) <->
  translates [] src ds /\ source_permitted allow src /\ valid_program [] ds sg.
Proof.
  split.
  - intros [fuel H]; destruct (compile_sound _ _ _ _ _ H) as [T [V [P W]]].
    split; [exact T|]; split; [apply (proj2 (translates_policy _ _ _ _ T)); exact P|exact V].
  - intros [T [P V]].
    apply (proj1 (translates_policy _ _ _ _ T)) in P.
    destruct (compile_complete _ _ _ _ T P V) as [bound B].
    exists bound; apply B; reflexivity.
Qed.

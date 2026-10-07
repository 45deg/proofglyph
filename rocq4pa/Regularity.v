From Stdlib Require Import List PeanoNat Compare_dec Lia.
From Rocq4pa Require Import Syntax Substitution WellFormed TypingSubstitution
  Kernel Completeness Confluence Generation Preservation.
Import ListNotations.

Lemma typing_signature_extension sg ctx t a extra : typing sg ctx t a ->
  typing (sg ++ extra) ctx t a.
Proof.
  intros H; induction H; eauto using typing.
  apply ty_const. rewrite nth_error_app1; [exact H|].
  apply nth_error_Some; rewrite H; discriminate.
Qed.

Theorem wf_signature_lookup sg n a : wf_signature sg -> nth_error sg n = Some a ->
  sorted_type sg [] a.
Proof.
  intros W; revert n a; induction W; intros n ty E.
  - destruct n; discriminate.
  - destruct (lt_dec n (length sg)) as [L|L].
    + rewrite nth_error_app1 in E by exact L.
      destruct (IHW _ _ E) as [k [T K]]. exists k; split; [apply typing_signature_extension; exact T|exact K].
    + rewrite nth_error_app2 in E by lia.
      destruct (n - length sg) as [|[|k]]; cbn in E; try discriminate.
      inversion E; subst; exists s; split; [apply typing_signature_extension; exact H|exact H0].
Qed.

Lemma sorted_type_any_context sg ctx a : wf_signature sg -> sorted_type sg [] a ->
  sorted_type sg ctx a.
Proof.
  intros W [s [T S]]. exists s; split; [|exact S].
  induction ctx as [|b ctx IH]; [exact T|].
  pose proof (typing_weaken _ _ _ _ b (wf_signature_closed _ W) IH) as WEAK.
  rewrite closed_rename in WEAK by exact (typing_subject_closed _ _ _ _ T).
  rewrite (rename_sort _ _ S) in WEAK; exact WEAK.
Qed.

Theorem wf_context_lookup sg ctx n a : wf_signature sg -> wf_context sg ctx ->
  nth_error ctx n = Some a -> typing sg ctx (shift (S n) 0 a) tType.
Proof.
  intros W C; revert n a; induction C; intros [|n] ty E; cbn in E; try discriminate.
  - inversion E; subst; rewrite shift_one.
    exact (typing_weaken _ _ _ _ ty (wf_signature_closed _ W) H).
  - rewrite <- rename_shift_succ.
    exact (typing_weaken _ _ _ _ a (wf_signature_closed _ W) (IHC _ _ E)).
Qed.

Lemma conv_pi_not_kind a b : ~ conv (tPi a b) tKind.
Proof.
  intros C; destruct (conv_joins _ _ C) as [u [PI K]].
  pose proof (steps_normal_form _ _ K nf_kind) as E; subst u.
  destruct (steps_pi_inv _ _ PI _ _ eq_refl) as [x [y [E _]]]; discriminate.
Qed.

Lemma instantiate_sort s x : is_sort s -> instantiate s x = s.
Proof. intros [-> | ->]; reflexivity. Qed.

(** Raw ty_conv can assign an untypable beta-expanded type. Regularity therefore
    gives a well-formed representative, not well-formedness of every raw target. *)
Theorem typing_regular_representative sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx t a -> exists proper,
    conv a proper /\ (proper = tKind \/ sorted_type sg ctx proper).
Proof.
  intros W CT T; revert CT.
  induction T as [ctx|ctx n a LOOK|ctx n a LOOK|
    ctx a b s A IHA B IHB IS|
    ctx a b bt s A IHA B IHB PI IHPI IS|
    ctx f x a b F IHF X IHX|ctx t a b T IH EQ]; intros CT.
  - exists tKind; split; [constructor|left; reflexivity].
  - exists (shift (S n) 0 a); split; [constructor|right].
    exists tType; split; [eapply wf_context_lookup; eauto|left; reflexivity].
  - exists a; split; [constructor|right].
    apply sorted_type_any_context; [exact W|eapply wf_signature_lookup; eauto].
  - exists s; split; [constructor|].
    destruct IS as [-> | ->]; [right; exists tKind; split; [constructor|right; reflexivity]|left; reflexivity].
  - exists (tPi a bt); split; [constructor|right; exists s; auto].
  - destruct (IHF CT) as [proper [EQ [K|[s [PT SORT]]]]].
    + subst proper; exfalso; eapply conv_pi_not_kind; exact EQ.
    + destruct (conv_joins _ _ EQ) as [u [PISTEP PSTEP]].
      destruct (steps_pi_inv _ _ PISTEP _ _ eq_refl) as [a' [b' [U [ASTEP BSTEP]]]].
      subst u.
      pose proof (subject_reduction_parallel_steps _ _ _ _ _ W PSTEP PT) as VALID.
      apply typing_generation in VALID; cbn [generates] in VALID.
      destruct VALID as [s' [AT [BT [SS SC]]]].
      assert (ARG : typing sg ctx x a') by (eapply ty_conv; [exact X|apply steps_conv; exact ASTEP]).
      exists (instantiate b' x); split.
      * rewrite !instantiate_as_substitute; apply conv_substitute; apply steps_conv; exact BSTEP.
      * right; exists s'; split; [|exact SS].
        rewrite <- (instantiate_sort s' x SS).
        eapply typing_instantiate; [exact W|exact BT|exact ARG].
  - destruct (IH CT) as [proper [C V]]. exists proper; split; [|exact V].
    eapply cv_trans; [apply cv_sym; exact EQ|exact C].
Qed.

From Stdlib Require Import List Bool Lia.
From Proofglyph.Language Require Import WeakNormalization Evaluation.
From Proofglyph.Language Require Export WeakKernelImpl.

Theorem whnf_relation fuel t u : whnf fuel t = Some u -> weak_head t u.
Proof.
  revert t u; induction fuel as [|n IH]; intros t u H; [discriminate|].
  destruct t; cbn [whnf bind] in H; try (inversion H; constructor; fail).
  destruct (whnf n t1) as [f|] eqn:F; try discriminate; cbn [bind] in H.
  destruct f; try (inversion H; subst; apply wh_app; [eapply IH; exact F|intros; discriminate]).
  eapply wh_beta; eauto.
Qed.

Theorem whnf_complete t u : weak_head t u ->
  eventually (fun fuel => whnf fuel t = Some u).
Proof.
  intros H; induction H;
    try (exists 1; intros [|fuel] L; [lia|reflexivity]).
  - next_fuel; cbn [whnf]; rewrite_successes.
    destruct f'; try reflexivity; exfalso; eapply H0; reflexivity.
  - next_fuel; cbn [whnf]; rewrite_successes; reflexivity.
Qed.

Lemma w_equal_relation fuel a b : w_equal fuel a b = true -> weak_compare a b.
Proof.
  revert a b; induction fuel as [|n IH]; intros a b H; cbn [w_equal] in H;
    destruct (term_eq_dec a b); [subst; apply wc_refl|discriminate|subst; apply wc_refl|].
  destruct (whnf n a) as [u|] eqn:U; try discriminate.
  destruct (whnf n b) as [v|] eqn:V; try discriminate.
  eapply wc_heads; [eapply whnf_relation; exact U|eapply whnf_relation; exact V|].
  destruct (term_eq_dec u v); [subst; apply wc_same|].
  destruct u; destruct v; try discriminate;
    apply andb_true_iff in H as [A B]; constructor; apply IH; assumption.
Qed.

Theorem w_equal_sound fuel a b : w_equal fuel a b = true -> conv a b.
Proof. intros H; apply weak_equal_sound; eapply w_equal_relation; exact H. Qed.

Lemma w_as_sort_relation fuel a s : w_as_sort fuel a = Some s -> weak_sort a s.
Proof.
  unfold w_as_sort, bind; destruct (whnf fuel a) eqn:A; [|discriminate].
  destruct (sortb t) eqn:S; [|discriminate]; intros H; inversion H; subst.
  split; [eapply whnf_relation; exact A|apply sortb_sound; exact S].
Qed.
Theorem w_as_sort_sound fuel a s : w_as_sort fuel a = Some s -> conv a s /\ is_sort s.
Proof. intros H; apply weak_as_sort_sound; eapply w_as_sort_relation; exact H. Qed.

Lemma w_equal_refl fuel t : w_equal fuel t t = true.
Proof. destruct fuel; cbn [w_equal]; destruct (term_eq_dec t t); congruence. Qed.

Lemma comparison_fuel_complete :
  (forall a b, weak_compare a b -> eventually (fun fuel => w_equal fuel a b = true)) /\
  (forall a b, weak_components a b -> eventually (fun fuel =>
    (if term_eq_dec a b then true else match a, b with
    | tPi a b, tPi c d | tLam a b, tLam c d | tApp a b, tApp c d =>
        w_equal fuel a c && w_equal fuel b d
    | _, _ => false end) = true)).
Proof.
  apply weak_comparison_ind.
  - intros; exists 0; intros; apply w_equal_refl.
  - intros a b u v A B C IC.
    pose proof (whnf_complete _ _ A); pose proof (whnf_complete _ _ B).
    next_fuel; cbn [w_equal]; destruct (term_eq_dec a b); [reflexivity|].
    rewrite_successes; reflexivity.
  - intros; exists 0; intros; destruct (term_eq_dec t t); congruence.
  - intros a b c d A IA B IB; combine_eventually.
    match goal with H : eventually _ |- _ => destruct H as [n N] end.
    exists n; intros fuel L; destruct (N fuel L) as [X Y].
    destruct (term_eq_dec (tPi a b) (tPi c d)); [reflexivity|]; rewrite X, Y; reflexivity.
  - intros a b c d A IA B IB; combine_eventually.
    match goal with H : eventually _ |- _ => destruct H as [n N] end.
    exists n; intros fuel L; destruct (N fuel L) as [X Y].
    destruct (term_eq_dec (tLam a b) (tLam c d)); [reflexivity|]; rewrite X, Y; reflexivity.
  - intros a b c d A IA B IB; combine_eventually.
    match goal with H : eventually _ |- _ => destruct H as [n N] end.
    exists n; intros fuel L; destruct (N fuel L) as [X Y].
    destruct (term_eq_dec (tApp a b) (tApp c d)); [reflexivity|]; rewrite X, Y; reflexivity.
Qed.

Theorem w_equal_complete a b : weak_compare a b ->
  eventually (fun fuel => w_equal fuel a b = true).
Proof. apply comparison_fuel_complete. Qed.

Theorem w_as_sort_complete a s : weak_sort a s ->
  eventually (fun fuel => w_as_sort fuel a = Some s).
Proof.
  intros [A S]; destruct (whnf_complete _ _ A) as [n N].
  exists n; intros fuel L; unfold w_as_sort; rewrite (N fuel L); cbn [bind].
  destruct S as [-> | ->]; reflexivity.
Qed.

Theorem whnf_monotone n m t u : n <= m -> whnf n t = Some u -> whnf m t = Some u.
Proof.
  revert m t u; induction n as [|n IH]; intros m t u L H; [discriminate|].
  destruct m as [|m]; [lia|]; assert (LE : n <= m) by lia.
  destruct t; cbn [whnf bind] in *; try assumption.
  destruct (whnf n t1) as [f|] eqn:F; try discriminate; cbn [bind] in H.
  rewrite (IH _ _ _ LE F); cbn [bind]; destruct f; try assumption; eapply IH; eauto.
Qed.
Theorem w_equal_monotone n m a b : n <= m -> w_equal n a b = true -> w_equal m a b = true.
Proof.
  revert m a b; induction n as [|n IH]; intros m a b L H;
    destruct m as [|m]; cbn [w_equal] in *;
    destruct (term_eq_dec a b); try reflexivity; try discriminate; [lia|].
  assert (LE : n <= m) by lia.
  destruct (whnf n a) as [u|] eqn:U; try discriminate.
  destruct (whnf n b) as [v|] eqn:V; try discriminate.
  rewrite (whnf_monotone _ _ _ _ LE U), (whnf_monotone _ _ _ _ LE V).
  destruct (term_eq_dec u v); [reflexivity|].
  destruct u; destruct v; try discriminate;
    apply andb_true_iff in H as [A B]; apply andb_true_iff; split; eapply IH; eauto.
Qed.
Theorem w_as_sort_monotone n m a s : n <= m -> w_as_sort n a = Some s -> w_as_sort m a = Some s.
Proof.
  intros L H; unfold w_as_sort, bind in *.
  destruct (whnf n a) eqn:A; try discriminate.
  rewrite (whnf_monotone _ _ _ _ L A); exact H.
Qed.

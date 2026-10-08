From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Tinyprover.Tp Require Export ResolveImpl.

Lemma lookup_sound x ns i : lookup x ns = Some i -> binds x ns i.
Proof.
  revert i; induction ns as [|n ns IH]; intros i H; cbn in H; [discriminate|].
  destruct (name_eq_dec n (Some x)) as [E|E].
  - subst; inversion H; constructor.
  - destruct (lookup x ns) eqn:L; inversion H; subst.
    constructor; [exact E|apply IH; reflexivity].
Qed.

Lemma lookup_complete x ns i : binds x ns i -> lookup x ns = Some i.
Proof.
  intros H; induction H; cbn -[name_eq_dec].
  - destruct (name_eq_dec (Some x) (Some x)); congruence.
  - destruct (name_eq_dec n (Some x)); [contradiction|].
    rewrite IHbinds; reflexivity.
Qed.

Lemma lookup_none x ns : lookup x ns = None <-> ~ In (Some x) ns.
Proof.
  induction ns as [|n ns IH]; cbn; [tauto|].
  destruct (name_eq_dec n (Some x)) as [E|E].
  - subst; split; [discriminate|intros H; exfalso; apply H; auto].
  - assert (N : (~ (n = Some x \/ In (Some x) ns)) <-> ~ In (Some x) ns) by tauto.
    rewrite N, <- IH.
    destruct (lookup x ns); cbn; split; intros H; congruence.
Qed.

Theorem resolve_sound gs ls e t : resolve gs ls e = Some t -> resolves gs ls e t.
Proof.
  revert ls t; induction e; intros ls t H; cbn in H.
  - destruct (lookup x ls) eqn:L.
    + inversion H; subst; constructor; apply lookup_sound; exact L.
    + destruct (lookup x (map (@Some string) gs)) eqn:G; inversion H; subst.
      apply resolves_global; [apply lookup_none; exact L|apply lookup_sound; exact G].
  - inversion H; constructor.
  - inversion H; constructor.
  - destruct (resolve gs ls e1) eqn:A; [|discriminate].
    destruct (resolve gs ls e2) eqn:B; inversion H; subst; constructor; auto.
  - destruct (resolve gs ls e1) eqn:A; [|discriminate].
    destruct (resolve gs (x :: ls) e2) eqn:B; inversion H; subst; constructor; auto.
  - destruct (resolve gs ls e1) eqn:A; [|discriminate].
    destruct (resolve gs (Some x :: ls) e2) eqn:B; inversion H; subst; constructor; auto.
Qed.

Theorem resolve_complete gs ls e t : resolves gs ls e t -> resolve gs ls e = Some t.
Proof.
  intros H; induction H; cbn; try rewrite IHresolves1, IHresolves2; try reflexivity.
  - rewrite (lookup_complete _ _ _ H); reflexivity.
  - rewrite (proj2 (lookup_none _ _) H), (lookup_complete _ _ _ H0); reflexivity.
Qed.

Theorem resolve_correct gs ls e t : resolve gs ls e = Some t <-> resolves gs ls e t.
Proof. split; [apply resolve_sound|apply resolve_complete]. Qed.

Corollary resolve_scoped gs ls e t :
  resolve gs ls e = Some t -> scoped (List.length gs) (List.length ls) t.
Proof. intros H; apply resolves_scoped with (e := e); apply resolve_sound; exact H. Qed.

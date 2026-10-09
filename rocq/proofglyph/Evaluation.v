From Stdlib Require Import List PeanoNat Lia.
From Proofglyph.Language Require Import Syntax Kernel.
From Proofglyph.Language Require Export EvaluationSpec.
Import ListNotations.

(** Successful computations are stable when the depth budget increases. *)
Theorem normal_monotone n m t u :
  n <= m -> normal n t = Some u -> normal m t = Some u.
Proof.
  revert m t u; induction n as [|n IH]; intros m t u LE H; [discriminate|].
  destruct m as [|m]; [lia|]. assert (L : n <= m) by lia.
  destruct t; cbn [normal] in *; unfold bind in *;
    repeat match type of H with
    | context [normal ?k ?x] =>
        let E := fresh "E" in destruct (normal k x) eqn:E; try discriminate;
        try (rewrite (IH m _ _ L E))
    end; try assumption.
  all: match type of H with context [match ?x with tType => _ | _ => _ end] =>
    destruct x; try assumption end.
  eapply IH; eauto.
Qed.

Theorem equal_monotone n m a b :
  n <= m -> equal n a b = true -> equal m a b = true.
Proof.
  intros L H; unfold equal in *.
  destruct (normal n a) eqn:A; try discriminate.
  destruct (normal n b) eqn:B; try discriminate.
  rewrite (normal_monotone _ _ _ _ L A), (normal_monotone _ _ _ _ L B); exact H.
Qed.

Theorem as_sort_monotone n m a s :
  n <= m -> as_sort n a = Some s -> as_sort m a = Some s.
Proof.
  intros L H; unfold as_sort, bind in *.
  destruct (normal n a) eqn:A; try discriminate.
  rewrite (normal_monotone _ _ _ _ L A); exact H.
Qed.

(** A bound works for EVERY larger fuel, rather than just one witness. *)
Definition eventually (P : nat -> Prop) := exists bound, forall fuel, bound <= fuel -> P fuel.

Lemma eventually_and P Q : eventually P -> eventually Q ->
  eventually (fun n => P n /\ Q n).
Proof.
  intros [p HP] [q HQ]; exists (Nat.max p q); intros n H; split;
    [apply HP|apply HQ]; lia.
Qed.

(** Fuel-free, finite big-step evaluation for this eager normalization strategy.
    This relation does not mention [normal] or existential fuel. *)
Theorem normal_complete t u : evaluates t u ->
  eventually (fun fuel => normal fuel t = Some u).
Proof.
  intros H; induction H.
  all: try (exists 1; intros [|fuel] L; [lia|reflexivity]).
  - destruct (eventually_and _ _ IHevaluates1 IHevaluates2) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A B]. cbn [normal]; rewrite A; cbn [bind]; rewrite B; reflexivity.
  - destruct (eventually_and _ _ IHevaluates1 IHevaluates2) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A B]. cbn [normal]; rewrite A; cbn [bind]; rewrite B; reflexivity.
  - destruct (eventually_and _ _ IHevaluates1 IHevaluates2) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A B]. cbn [normal]; rewrite A; cbn [bind]; rewrite B.
    destruct f'; try reflexivity. exfalso; eapply H1; reflexivity.
  - destruct (eventually_and _ _ IHevaluates1
      (eventually_and _ _ IHevaluates2 IHevaluates3)) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A [B C]].
    cbn [normal]; rewrite A; cbn [bind]; rewrite B; exact C.
Qed.

Theorem equal_complete a b u : evaluates a u -> evaluates b u ->
  eventually (fun fuel => equal fuel a b = true).
Proof.
  intros A B.
  destruct (eventually_and _ _ (normal_complete _ _ A) (normal_complete _ _ B)) as [k HK].
  exists k; intros n L; destruct (HK n L) as [NA NB].
  unfold equal; rewrite NA, NB; destruct (term_eq_dec u u); congruence.
Qed.

Theorem as_sort_complete a s : evaluates a s -> is_sort s ->
  eventually (fun fuel => as_sort fuel a = Some s).
Proof.
  intros A S; destruct (normal_complete _ _ A) as [k HK].
  exists k; intros n L; unfold as_sort; rewrite (HK n L); cbn [bind].
  destruct S as [-> | ->]; reflexivity.
Qed.

Ltac combine_eventually :=
  repeat match goal with
  | H1 : eventually ?P, H2 : eventually ?Q |- _ =>
      let H := fresh "combined" in
      pose proof (eventually_and P Q H1 H2) as H; clear H1 H2
  end.

Ltac next_fuel :=
  combine_eventually;
  match goal with H : eventually _ |- _ =>
    let k := fresh "bound" in let HK := fresh "bounded" in
    destruct H as [k HK]; exists (S k);
    intros [|fuel] LE; [lia|]; specialize (HK fuel ltac:(lia));
    repeat match goal with H : _ /\ _ |- _ => destruct H end
  end.

Ltac rewrite_successes :=
  repeat match goal with H : ?x = Some ?v |- context [?x] => rewrite H; cbn [bind] end;
  repeat match goal with H : ?x = true |- context [?x] => rewrite H; cbn [bind] end.

Theorem normal_evaluates fuel t u : normal fuel t = Some u -> evaluates t u.
Proof.
  revert t u; induction fuel as [|n IH]; intros t u H; [discriminate|].
  destruct t as [| |i|i|a b|a b|f x]; cbn [normal bind] in H.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; constructor.
  - split_options; inversion H; subst; constructor; eauto.
  - split_options; inversion H; subst; constructor; eauto.
  - destruct (normal n f) as [f'|] eqn:F; try discriminate.
    cbn [bind] in H.
    destruct (normal n x) as [x'|] eqn:X; try discriminate.
    cbn [bind] in H.
    pose proof (IH _ _ F) as EF.
    pose proof (IH _ _ X) as EX.
    destruct f'; try (inversion H; subst; apply ev_app; auto; intros; discriminate).
    eapply ev_beta; eauto.
Qed.

Theorem normalization_iff t u :
  evaluates t u <-> exists fuel, normal fuel t = Some u.
Proof.
  split.
  - intros H; destruct (normal_complete _ _ H) as [k HK]; exists k; apply HK; reflexivity.
  - intros [fuel H]; eapply normal_evaluates; eauto.
Qed.

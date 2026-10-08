From Stdlib Require Import List Permutation.
Import ListNotations.

(** Independent propositional calculi. No LF terms or exporter code are used. *)
Inductive formula :=
| Atom (i : nat) | Bottom | Top
| Imp (a b : formula) | Conj (a b : formula) | Disj (a b : formula)
| Neg (a : formula).

Inductive NK : list formula -> formula -> Prop :=
| nk_assume : forall g a, In a g -> NK g a
| nk_top : forall g, NK g Top
| nk_bottom : forall g a, NK g Bottom -> NK g a
| nk_imp_intro : forall g a b, NK (a :: g) b -> NK g (Imp a b)
| nk_imp_elim : forall g a b, NK g (Imp a b) -> NK g a -> NK g b
| nk_conj_intro : forall g a b, NK g a -> NK g b -> NK g (Conj a b)
| nk_conj_left : forall g a b, NK g (Conj a b) -> NK g a
| nk_conj_right : forall g a b, NK g (Conj a b) -> NK g b
| nk_disj_left : forall g a b, NK g a -> NK g (Disj a b)
| nk_disj_right : forall g a b, NK g b -> NK g (Disj a b)
| nk_disj_elim : forall g a b c, NK g (Disj a b) -> NK (a :: g) c -> NK (b :: g) c -> NK g c
| nk_neg_intro : forall g a, NK (a :: g) Bottom -> NK g (Neg a)
| nk_neg_elim : forall g a, NK g (Neg a) -> NK g a -> NK g Bottom
| nk_classical : forall g a, NK (Neg a :: g) Bottom -> NK g a.

(** Context-sharing LK. Weakening/contraction make the shared-context logical
    and cut rules equivalent to the usual split-context formulation. *)
Inductive LK : list formula -> list formula -> Prop :=
| lk_identity : forall a, LK [a] [a]
| lk_bottom : forall g d, LK (Bottom :: g) d
| lk_top : forall g d, LK g (Top :: d)
| lk_weak_left : forall g d a, LK g d -> LK (a :: g) d
| lk_weak_right : forall g d a, LK g d -> LK g (a :: d)
| lk_contract_left : forall g d a, LK (a :: a :: g) d -> LK (a :: g) d
| lk_contract_right : forall g d a, LK g (a :: a :: d) -> LK g (a :: d)
| lk_exchange_left : forall g h d, Permutation g h -> LK g d -> LK h d
| lk_exchange_right : forall g h d, Permutation d h -> LK g d -> LK g h
| lk_imp_right : forall g d a b, LK (a :: g) (b :: d) -> LK g (Imp a b :: d)
| lk_imp_left : forall g d a b, LK g (a :: d) -> LK (b :: g) d -> LK (Imp a b :: g) d
| lk_conj_left : forall g d a b, LK (a :: b :: g) d -> LK (Conj a b :: g) d
| lk_conj_right : forall g d a b, LK g (a :: d) -> LK g (b :: d) -> LK g (Conj a b :: d)
| lk_disj_left : forall g d a b, LK (a :: g) d -> LK (b :: g) d -> LK (Disj a b :: g) d
| lk_disj_right : forall g d a b, LK g (a :: b :: d) -> LK g (Disj a b :: d)
| lk_neg_left : forall g d a, LK g (a :: d) -> LK (Neg a :: g) d
| lk_neg_right : forall g d a, LK (a :: g) d -> LK g (Neg a :: d)
| lk_cut : forall g d a, LK g (a :: d) -> LK (a :: g) d -> LK g d.

Fixpoint holds (v : nat -> Prop) f : Prop := match f with
| Atom i => v i | Bottom => False | Top => True
| Imp a b => holds v a -> holds v b
| Conj a b => holds v a /\ holds v b
| Disj a b => holds v a \/ holds v b
| Neg a => ~ holds v a
end.
Definition all_hold v g := forall a, In a g -> holds v a.
Definition some_hold v d := exists a, In a d /\ holds v a.

Section Soundness.
Variable v : nat -> Prop.
(** Classical reasoning is an explicit parameter, not a new global axiom. *)
Variable classic : forall P : Prop, P \/ ~ P.

Lemma all_cons a g : all_hold v (a :: g) <-> holds v a /\ all_hold v g.
Proof.
  unfold all_hold; simpl; split.
  - intros H; split; [apply H; auto|intros b IN; apply H; auto].
  - intros [A G] b [E|IN]; [subst; exact A|apply G; exact IN].
Qed.
Lemma some_cons a d : some_hold v (a :: d) <-> holds v a \/ some_hold v d.
Proof.
  unfold some_hold; simpl; split.
  - intros [b [[E|IN] B]]; [subst; auto|right; exists b; auto].
  - intros [A|[b [IN B]]]; [exists a|exists b]; auto.
Qed.
Lemma all_perm g h : Permutation g h -> all_hold v g <-> all_hold v h.
Proof.
  intros P; unfold all_hold; split; intros H a IN; apply H.
  - eapply Permutation_in; [apply Permutation_sym; exact P|exact IN].
  - eapply Permutation_in; eauto.
Qed.
Lemma some_perm g h : Permutation g h -> some_hold v g <-> some_hold v h.
Proof.
  intros P; unfold some_hold; split; intros [a [IN A]]; exists a; split; auto.
  - eapply Permutation_in; eauto.
  - eapply Permutation_in; [apply Permutation_sym; exact P|exact IN].
Qed.

Theorem NK_sound g a : NK g a -> all_hold v g -> holds v a.
Proof.
  intros H; induction H; intros G; cbn [holds] in *.
  - apply G; assumption.
  - exact I.
  - exfalso; auto.
  - intros A; apply IHNK; apply all_cons; auto.
  - apply IHNK1; auto.
  - auto.
  - apply (proj1 (IHNK G)).
  - apply (proj2 (IHNK G)).
  - auto.
  - auto.
  - destruct (IHNK1 G) as [A|B]; [apply IHNK2|apply IHNK3]; apply all_cons; auto.
  - intros A; apply IHNK; apply all_cons; auto.
  - apply (IHNK1 G); auto.
  - destruct (classic (holds v a)) as [A|N]; [exact A|].
    exfalso; apply IHNK; apply all_cons; auto.
Qed.

Theorem LK_sound g d : LK g d -> all_hold v g -> some_hold v d.
Proof.
  intros H; induction H; intros G.
  - apply some_cons; left; exact (proj1 (proj1 (all_cons a []) G)).
  - apply all_cons in G as [B _]; contradiction.
  - apply some_cons; left; exact I.
  - apply IHLK; apply all_cons in G; tauto.
  - apply some_cons; right; auto.
  - apply IHLK; apply all_cons in G as [A G]; apply all_cons; split; auto.
    apply all_cons; auto.
  - apply some_cons; apply IHLK in G; apply some_cons in G as [A|G]; auto.
    apply some_cons in G; tauto.
  - apply IHLK; apply (proj2 (all_perm _ _ H)); exact G.
  - apply (proj1 (some_perm _ _ H)); auto.
  - apply some_cons; cbn [holds].
    destruct (classic (holds v a)) as [A|N]; [|left; tauto].
    assert (T : some_hold v (b :: d)) by (apply IHLK; apply all_cons; auto).
    apply some_cons in T; tauto.
  - apply all_cons in G as [AB G]; cbn [holds] in AB.
    specialize (IHLK1 G); apply some_cons in IHLK1 as [A|D]; auto.
    apply IHLK2; apply all_cons; auto.
  - apply all_cons in G as [[A B] G]; apply IHLK.
    apply all_cons; split; auto; apply all_cons; auto.
  - specialize (IHLK1 G); specialize (IHLK2 G).
    apply some_cons in IHLK1; apply some_cons in IHLK2.
    apply some_cons; cbn [holds]; tauto.
  - apply all_cons in G as [[A|B] G]; [apply IHLK1|apply IHLK2]; apply all_cons; auto.
  - apply IHLK in G; apply some_cons in G as [A|G]; apply some_cons; cbn [holds]; auto.
    apply some_cons in G; tauto.
  - apply all_cons in G as [N G]; cbn [holds] in N.
    specialize (IHLK G); apply some_cons in IHLK; tauto.
  - apply some_cons; cbn [holds].
    destruct (classic (holds v a)) as [A|N]; auto.
    right; apply IHLK; apply all_cons; auto.
  - specialize (IHLK1 G); apply some_cons in IHLK1 as [A|D]; auto.
    apply IHLK2; apply all_cons; auto.
Qed.
End Soundness.

Example NK_identity a : NK [] (Imp a a).
Proof. apply nk_imp_intro; apply nk_assume; simpl; auto. Qed.
Example LK_identity a : LK [] [Imp a a].
Proof. apply lk_imp_right; apply lk_identity. Qed.

Print Assumptions NK_sound.
Print Assumptions LK_sound.

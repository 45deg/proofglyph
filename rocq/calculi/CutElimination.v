From Stdlib Require Import List Permutation PeanoNat Lia Arith.Wf_nat.
From Tinyprover.Calculi Require Import Calculi.
Import ListNotations.

(** The same context-sharing LK, with no cut constructor. *)
Inductive LK_cut_free : list formula -> list formula -> Prop :=
| cf_identity : forall a, LK_cut_free [a] [a]
| cf_bottom : forall g d, LK_cut_free (Bottom :: g) d
| cf_top : forall g d, LK_cut_free g (Top :: d)
| cf_weak_left : forall g d a, LK_cut_free g d -> LK_cut_free (a :: g) d
| cf_weak_right : forall g d a, LK_cut_free g d -> LK_cut_free g (a :: d)
| cf_contract_left : forall g d a, LK_cut_free (a :: a :: g) d -> LK_cut_free (a :: g) d
| cf_contract_right : forall g d a, LK_cut_free g (a :: a :: d) -> LK_cut_free g (a :: d)
| cf_exchange_left : forall g h d, Permutation g h -> LK_cut_free g d -> LK_cut_free h d
| cf_exchange_right : forall g h d, Permutation d h -> LK_cut_free g d -> LK_cut_free g h
| cf_imp_right : forall g d a b, LK_cut_free (a :: g) (b :: d) -> LK_cut_free g (Imp a b :: d)
| cf_imp_left : forall g d a b, LK_cut_free g (a :: d) -> LK_cut_free (b :: g) d -> LK_cut_free (Imp a b :: g) d
| cf_conj_left : forall g d a b, LK_cut_free (a :: b :: g) d -> LK_cut_free (Conj a b :: g) d
| cf_conj_right : forall g d a b, LK_cut_free g (a :: d) -> LK_cut_free g (b :: d) -> LK_cut_free g (Conj a b :: d)
| cf_disj_left : forall g d a b, LK_cut_free (a :: g) d -> LK_cut_free (b :: g) d -> LK_cut_free (Disj a b :: g) d
| cf_disj_right : forall g d a b, LK_cut_free g (a :: b :: d) -> LK_cut_free g (Disj a b :: d)
| cf_neg_left : forall g d a, LK_cut_free g (a :: d) -> LK_cut_free (Neg a :: g) d
| cf_neg_right : forall g d a, LK_cut_free (a :: g) d -> LK_cut_free g (Neg a :: d).

Theorem cut_free_is_LK g d : LK_cut_free g d -> LK g d.
Proof. intros H; induction H; eauto using LK. Qed.

Definition boolean_interpretation (v : nat -> bool) i := v i = true.
Definition boolean_valid g d := forall v,
  all_hold (boolean_interpretation v) g -> some_hold (boolean_interpretation v) d.

Lemma boolean_holds_dec v a :
  {holds (boolean_interpretation v) a} + {~ holds (boolean_interpretation v) a}.
Proof.
  induction a; cbn [holds boolean_interpretation] in *.
  - change ({v i = true} + {v i <> true}); destruct (v i); [left; reflexivity|right; discriminate].
  - auto.
  - auto.
  - destruct IHa1, IHa2; [left|right|left|left]; tauto.
  - destruct IHa1, IHa2; try (left; tauto); right; tauto.
  - destruct IHa1, IHa2; try (left; tauto); right; tauto.
  - destruct IHa; [right|left]; tauto.
Defined.

Theorem LK_boolean_sound g d : LK g d -> boolean_valid g d.
Proof.
  intros H; induction H; intros valuation G;
    try specialize (IHLK valuation);
    try specialize (IHLK1 valuation);
    try specialize (IHLK2 valuation).
  - apply some_cons; left; exact (proj1 (proj1 (all_cons (boolean_interpretation valuation) a []) G)).
  - apply all_cons in G as [B _]; contradiction.
  - apply some_cons; left; exact I.
  - apply IHLK; apply all_cons in G; tauto.
  - apply some_cons; right; auto.
  - apply IHLK; apply all_cons in G as [A G]; apply all_cons; split; auto.
    apply all_cons; auto.
  - apply some_cons; apply IHLK in G; apply some_cons in G as [A|G]; auto.
    apply some_cons in G; tauto.
  - apply IHLK; apply (proj2 (all_perm _ _ _ H)); exact G.
  - apply (proj1 (some_perm _ _ _ H)); auto.
  - apply some_cons; cbn [holds].
    destruct (boolean_holds_dec valuation a) as [A|N]; [|left; tauto].
    assert (T : some_hold (boolean_interpretation valuation) (b :: d)) by (apply IHLK; apply all_cons; auto).
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
    destruct (boolean_holds_dec valuation a) as [A|N]; auto.
    right; apply IHLK; apply all_cons; auto.
  - specialize (IHLK1 G); apply some_cons in IHLK1 as [A|D]; auto.
    apply IHLK2; apply all_cons; auto.
Qed.

Fixpoint formula_weight a := match a with
| Atom _ => 0 | Bottom | Top => 1
| Imp a b | Conj a b | Disj a b => S (formula_weight a + formula_weight b)
| Neg a => S (formula_weight a)
end.
Fixpoint context_weight g := match g with
| [] => 0 | a :: g => formula_weight a + context_weight g
end.
Definition atomic a := match a with Atom _ => True | _ => False end.

Lemma weight_permutation g h : Permutation g h -> context_weight g = context_weight h.
Proof. intros H; induction H; cbn [context_weight]; lia. Qed.
Lemma atomic_or_focus g : Forall atomic g \/
  exists a h, ~ atomic a /\ Permutation g (a :: h).
Proof.
  induction g as [|a g IH]; [left; constructor|].
  assert (DEC : {atomic a} + {~ atomic a}) by (destruct a; cbn [atomic]; tauto).
  destruct DEC as [A|A].
  - destruct IH as [G|[b [h [B P]]]].
    + left; constructor; assumption.
    + right; exists b, (a :: h); split; [exact B|].
      eapply Permutation_trans; [apply perm_skip; exact P|apply perm_swap].
  - right; exists a, g; split; [exact A|reflexivity].
Qed.

Lemma valid_permutation g h d e : Permutation g h -> Permutation d e ->
  boolean_valid g d -> boolean_valid h e.
Proof.
  intros G D V v A; apply (proj1 (some_perm _ _ _ D)); apply V.
  apply (proj2 (all_perm _ _ _ G)); exact A.
Qed.

Lemma cf_weak_left_list g h d : LK_cut_free g d -> LK_cut_free (h ++ g) d.
Proof. intros P; induction h; simpl; eauto using cf_weak_left. Qed.
Lemma cf_weak_right_list g d e : LK_cut_free g d -> LK_cut_free g (e ++ d).
Proof. intros P; induction e; simpl; eauto using cf_weak_right. Qed.
Lemma permutation_last_head (a : formula) g : Permutation (g ++ [a]) (a :: g).
Proof.
  pose proof (Permutation_middle g [] a) as P; rewrite app_nil_r in P.
  apply Permutation_sym; exact P.
Qed.
Lemma cf_identity_head a g d : LK_cut_free (a :: g) (a :: d).
Proof.
  eapply cf_exchange_left with (g := g ++ [a]).
  - apply permutation_last_head.
  - eapply cf_exchange_right with (d := d ++ [a]).
    + apply permutation_last_head.
    + apply cf_weak_left_list; apply cf_weak_right_list; apply cf_identity.
Qed.
Lemma cf_identity_in a g d : In a g -> In a d -> LK_cut_free g d.
Proof.
  intros G D; apply in_split in G as [g1 [g2 ->]], D as [d1 [d2 ->]].
  eapply cf_exchange_left; [apply Permutation_middle|].
  eapply cf_exchange_right; [apply Permutation_middle|].
  apply cf_identity_head.
Qed.

Lemma atomic_valid_cut_free g d : Forall atomic g -> Forall atomic d ->
  boolean_valid g d -> LK_cut_free g d.
Proof.
  intros G D V.
  set (v := fun i => if in_dec Nat.eq_dec i
    (flat_map (fun a => match a with Atom j => [j] | _ => [] end) g)
    then true else false).
  assert (VG : all_hold (boolean_interpretation v) g).
  { intros a IN; pose proof (proj1 (Forall_forall _ _) G a IN) as A.
    destruct a; cbn [atomic] in A; try contradiction.
    cbn [holds]; unfold boolean_interpretation, v.
    destruct (in_dec Nat.eq_dec i _) as [YES|NO]; [reflexivity|].
    exfalso; apply NO; apply in_flat_map; exists (Atom i); simpl; auto. }
  destruct (V v VG) as [a [IN A]].
  pose proof (proj1 (Forall_forall _ _) D a IN) as AT.
  destruct a; cbn [atomic] in AT; try contradiction.
  cbn [holds] in A; unfold boolean_interpretation, v in A.
  destruct (in_dec Nat.eq_dec i _) as [YES|NO]; [|discriminate].
  apply in_flat_map in YES as [a [AG AI]].
  destruct a; simpl in AI; try contradiction.
  destruct AI as [E|E]; [subst|contradiction].
  eapply cf_identity_in; eassumption.
Qed.

(** Invertibility of logical rules at the level of Boolean semantics. *)
Ltac unpack_semantics :=
  repeat rewrite all_cons in *; repeat rewrite some_cons in *;
  cbn [holds] in *.

Lemma valid_top_left g d : boolean_valid (Top :: g) d -> boolean_valid g d.
Proof. intros V v G; apply V; apply all_cons; cbn [holds]; auto. Qed.
Lemma valid_bottom_right g d : boolean_valid g (Bottom :: d) -> boolean_valid g d.
Proof. intros V v G; specialize (V v G); unpack_semantics; tauto. Qed.
Lemma valid_imp_left_a g d a b : boolean_valid (Imp a b :: g) d ->
  boolean_valid g (a :: d).
Proof.
  intros V v G; destruct (boolean_holds_dec v a) as [A|A]; apply some_cons; auto.
  right; apply V; apply all_cons; cbn [holds]; tauto.
Qed.
Lemma valid_imp_left_b g d a b : boolean_valid (Imp a b :: g) d ->
  boolean_valid (b :: g) d.
Proof. intros V v G; apply V; unpack_semantics; tauto. Qed.
Lemma valid_imp_right g d a b : boolean_valid g (Imp a b :: d) ->
  boolean_valid (a :: g) (b :: d).
Proof.
  intros V v G; apply all_cons in G as [A G]; specialize (V v G).
  unpack_semantics; tauto.
Qed.
Lemma valid_conj_left g d a b : boolean_valid (Conj a b :: g) d ->
  boolean_valid (a :: b :: g) d.
Proof. intros V v G; apply V; unpack_semantics; tauto. Qed.
Lemma valid_conj_right_a g d a b : boolean_valid g (Conj a b :: d) ->
  boolean_valid g (a :: d).
Proof. intros V v G; specialize (V v G); unpack_semantics; tauto. Qed.
Lemma valid_conj_right_b g d a b : boolean_valid g (Conj a b :: d) ->
  boolean_valid g (b :: d).
Proof. intros V v G; specialize (V v G); unpack_semantics; tauto. Qed.
Lemma valid_disj_left_a g d a b : boolean_valid (Disj a b :: g) d ->
  boolean_valid (a :: g) d.
Proof. intros V v G; apply V; unpack_semantics; tauto. Qed.
Lemma valid_disj_left_b g d a b : boolean_valid (Disj a b :: g) d ->
  boolean_valid (b :: g) d.
Proof. intros V v G; apply V; unpack_semantics; tauto. Qed.
Lemma valid_disj_right g d a b : boolean_valid g (Disj a b :: d) ->
  boolean_valid g (a :: b :: d).
Proof. intros V v G; specialize (V v G); unpack_semantics; tauto. Qed.
Lemma valid_neg_left g d a : boolean_valid (Neg a :: g) d ->
  boolean_valid g (a :: d).
Proof.
  intros V v G; destruct (boolean_holds_dec v a) as [A|A]; apply some_cons; auto.
  right; apply V; apply all_cons; cbn [holds]; auto.
Qed.
Lemma valid_neg_right g d a : boolean_valid g (Neg a :: d) ->
  boolean_valid (a :: g) d.
Proof.
  intros V v G; apply all_cons in G as [A G]; specialize (V v G).
  unpack_semantics; tauto.
Qed.

Theorem boolean_valid_cut_free g d : boolean_valid g d -> LK_cut_free g d.
Proof.
  remember (context_weight g + context_weight d) as n eqn:E.
  revert g d E; induction n using lt_wf_ind; intros g d E V.
  destruct (atomic_or_focus g) as [G|[a [h [A P]]]].
  - destruct (atomic_or_focus d) as [D|[a [h [A P]]]].
    + apply atomic_valid_cut_free; assumption.
    + assert (W : context_weight g + context_weight (a :: h) = n)
        by (rewrite <- (weight_permutation _ _ P); lia).
      assert (VH : boolean_valid g (a :: h))
        by (eapply valid_permutation; [reflexivity|exact P|exact V]).
      eapply cf_exchange_right; [apply Permutation_sym; exact P|].
      destruct a; cbn [atomic] in A; try contradiction;
        cbn [context_weight formula_weight] in W.
      * apply cf_weak_right. eapply H; [|reflexivity|apply valid_bottom_right; exact VH]; lia.
      * apply cf_top.
      * apply cf_imp_right. eapply H; [|reflexivity|apply valid_imp_right; exact VH]; cbn [context_weight]; lia.
      * apply cf_conj_right.
        -- eapply H; [|reflexivity|eapply valid_conj_right_a; exact VH]; cbn [context_weight]; lia.
        -- eapply H; [|reflexivity|eapply valid_conj_right_b; exact VH]; cbn [context_weight]; lia.
      * apply cf_disj_right. eapply H; [|reflexivity|apply valid_disj_right; exact VH]; cbn [context_weight]; lia.
      * apply cf_neg_right. eapply H; [|reflexivity|apply valid_neg_right; exact VH]; cbn [context_weight]; lia.
  - assert (W : context_weight (a :: h) + context_weight d = n)
      by (rewrite <- (weight_permutation _ _ P); lia).
    assert (VH : boolean_valid (a :: h) d)
      by (eapply valid_permutation; [exact P|reflexivity|exact V]).
    eapply cf_exchange_left; [apply Permutation_sym; exact P|].
    destruct a; cbn [atomic] in A; try contradiction;
      cbn [context_weight formula_weight] in W.
    + apply cf_bottom.
    + apply cf_weak_left. eapply H; [|reflexivity|apply valid_top_left; exact VH]; lia.
    + apply cf_imp_left.
      * eapply H; [|reflexivity|eapply valid_imp_left_a; exact VH]; cbn [context_weight]; lia.
      * eapply H; [|reflexivity|eapply valid_imp_left_b; exact VH]; cbn [context_weight]; lia.
    + apply cf_conj_left. eapply H; [|reflexivity|apply valid_conj_left; exact VH]; cbn [context_weight]; lia.
    + apply cf_disj_left.
      * eapply H; [|reflexivity|eapply valid_disj_left_a; exact VH]; cbn [context_weight]; lia.
      * eapply H; [|reflexivity|eapply valid_disj_left_b; exact VH]; cbn [context_weight]; lia.
    + apply cf_neg_left. eapply H; [|reflexivity|apply valid_neg_left; exact VH]; cbn [context_weight]; lia.
Qed.

Theorem LK_cut_elimination g d : LK g d -> LK_cut_free g d.
Proof. intros H; apply boolean_valid_cut_free; apply LK_boolean_sound; exact H. Qed.
Corollary LK_cut_admissible g d a :
  LK_cut_free g (a :: d) -> LK_cut_free (a :: g) d -> LK_cut_free g d.
Proof.
  intros P Q; apply LK_cut_elimination; eapply lk_cut;
    apply cut_free_is_LK; eassumption.
Qed.

Print Assumptions boolean_valid_cut_free.
Print Assumptions LK_cut_elimination.
Print Assumptions LK_cut_admissible.

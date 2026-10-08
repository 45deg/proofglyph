From Stdlib Require Import List Permutation PeanoNat.
From Tinyprover.Pa Require Import Syntax Program.
From Tinyprover.Calculi Require Import Calculi Encoding Verification.
Import ListNotations.

(** Closed encodings can be substituted under any number of LF binders. *)
Lemma shift_index_code delta cutoff i :
  shift delta cutoff (encode_index i) = encode_index i.
Proof. induction i; simpl; congruence. Qed.
Lemma subst_index_code depth value i :
  subst depth value (encode_index i) = encode_index i.
Proof. induction i; simpl; congruence. Qed.
Lemma shift_formula_code delta cutoff a :
  shift delta cutoff (encode a) = encode a.
Proof.
  induction a; cbn [encode code_binary shift];
    try rewrite shift_index_code; try congruence.
  all: unfold code_binary in *; cbn [shift]; congruence.
Qed.
Lemma subst_formula_code depth value a :
  subst depth value (encode a) = encode a.
Proof.
  induction a; cbn [encode code_binary subst];
    try rewrite subst_index_code; try congruence.
  all: unfold code_binary in *; cbn [subst]; congruence.
Qed.
Lemma shift_context_code delta cutoff g :
  shift delta cutoff (encode_context g) = encode_context g.
Proof.
  induction g; cbn [encode_context code_binary shift];
    try rewrite shift_formula_code; try congruence.
  all: unfold code_binary in *; cbn [shift]; try rewrite shift_formula_code; congruence.
Qed.
Lemma subst_context_code depth value g :
  subst depth value (encode_context g) = encode_context g.
Proof.
  induction g; cbn [encode_context code_binary subst];
    try rewrite subst_formula_code; try congruence.
  all: unfold code_binary in *; cbn [subst]; try rewrite subst_formula_code; congruence.
Qed.

Definition lf a t := typing fixed_signature [] t a.
Definition member_type a g := code_binary 14 (encode a) (encode_context g).
Definition permutation_type g h := code_binary 17 (encode_context g) (encode_context h).
Definition NK_code g a := nk_type (encode_context g) (encode a).
Definition LK_code g d := lk_type (encode_context g) (encode_context d).

(** These tactics only construct declarative typing derivations. Computation
    checks constant lookup, never assumes a rule or a typing conclusion. *)
Ltac lf_constant n :=
  let a := eval vm_compute in (nth n fixed_signature tType) in
  let E := fresh "lookup" in
  assert (E : nth_error fixed_signature n = Some a) by (vm_compute; reflexivity);
  let H := fresh "typed" in
  pose proof (ty_const fixed_signature [] n a E) as H; clear E.

Ltac lf_argument X :=
  match goal with
  | F : typing fixed_signature [] ?f (tPi ?a ?b) |- _ =>
    let H := fresh "typed" in
    pose proof (ty_app fixed_signature [] f _ a b F X) as H;
    cbn [instantiate subst shift Nat.eqb Nat.ltb Nat.leb Nat.add Nat.pred] in H;
    repeat rewrite shift_formula_code in H;
    repeat rewrite shift_context_code in H;
    repeat rewrite shift_index_code in H;
    repeat rewrite subst_formula_code in H;
    repeat rewrite subst_context_code in H;
    repeat rewrite subst_index_code in H;
    clear F
  end.

Lemma index_code_typed i : lf (tConst 0) (encode_index i).
Proof.
  unfold lf; induction i; cbn [encode_index].
  - lf_constant 1; assumption.
  - lf_constant 2; lf_argument IHi; assumption.
Qed.

Lemma formula_code_typed a : lf (tConst 3) (encode a).
Proof.
  unfold lf; induction a; cbn [encode code_binary].
  - pose proof (index_code_typed i) as I; unfold lf in I.
    lf_constant 4; lf_argument I; assumption.
  - lf_constant 5; assumption.
  - lf_constant 6; assumption.
  - lf_constant 7; lf_argument IHa1; lf_argument IHa2; assumption.
  - lf_constant 8; lf_argument IHa1; lf_argument IHa2; assumption.
  - lf_constant 9; lf_argument IHa1; lf_argument IHa2; assumption.
  - lf_constant 10; lf_argument IHa; assumption.
Qed.

Lemma context_code_typed g : lf (tConst 11) (encode_context g).
Proof.
  unfold lf; induction g as [|a g IH]; cbn [encode_context code_binary].
  - lf_constant 12; assumption.
  - pose proof (formula_code_typed a) as A; unfold lf in A.
    lf_constant 13; lf_argument A; lf_argument IH; assumption.
Qed.

Definition rule_app n args := fold_left tApp args (tConst n).

Ltac lf_formula a :=
  let H := fresh "formula_typed" in
  pose proof (formula_code_typed a) as H; unfold lf in H; lf_argument H.
Ltac lf_context g :=
  let H := fresh "context_typed" in
  pose proof (context_code_typed g) as H; unfold lf in H; lf_argument H.
Ltac lf_finish :=
  unfold member_type, permutation_type, NK_code, LK_code, nk_type, lk_type,
    rule_app, code_binary;
  cbn [encode encode_context fold_left code_binary] in *; assumption.

Lemma NK_code_is_type g a : lf tType (NK_code g a).
Proof.
  unfold lf; lf_constant 22; lf_context g; lf_formula a; lf_finish.
Qed.
Lemma LK_code_is_type g d : lf tType (LK_code g d).
Proof.
  unfold lf; lf_constant 37; lf_context g; lf_context d; lf_finish.
Qed.

(** Each LF rule is checked against the actual exported signature. *)
Lemma encoded_in_here a g :
  lf (member_type a (a :: g)) (rule_app 15 [(encode a); (encode_context g)]).
Proof.
  unfold lf in *.
  lf_constant 15; lf_formula a; lf_context g; lf_finish.
Qed.

Lemma encoded_in_there a b g p0 :
  lf (member_type a g) p0 ->
  lf (member_type a (b :: g)) (rule_app 16 [(encode a); (encode b); (encode_context g); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 16; lf_formula a; lf_formula b; lf_context g; lf_argument P0; lf_finish.
Qed.

Lemma encoded_perm_nil  :
  lf (permutation_type [] []) (rule_app 18 []).
Proof.
  unfold lf in *.
  lf_constant 18; lf_finish.
Qed.

Lemma encoded_perm_cons a g h p0 :
  lf (permutation_type g h) p0 ->
  lf (permutation_type (a :: g) (a :: h)) (rule_app 19 [(encode a); (encode_context g); (encode_context h); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 19; lf_formula a; lf_context g; lf_context h; lf_argument P0; lf_finish.
Qed.

Lemma encoded_perm_swap b a g :
  lf (permutation_type (b :: a :: g) (a :: b :: g)) (rule_app 20 [(encode b); (encode a); (encode_context g)]).
Proof.
  unfold lf in *.
  lf_constant 20; lf_formula b; lf_formula a; lf_context g; lf_finish.
Qed.

Lemma encoded_perm_trans g h d p0 p1 :
  lf (permutation_type g h) p0 ->
  lf (permutation_type h d) p1 ->
  lf (permutation_type g d) (rule_app 21 [(encode_context g); (encode_context h); (encode_context d); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 21; lf_context g; lf_context h; lf_context d; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_nk_assume g a p0 :
  lf (member_type a g) p0 ->
  lf (NK_code g a) (rule_app 23 [(encode_context g); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 23; lf_context g; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_top g :
  lf (NK_code g Top) (rule_app 24 [(encode_context g)]).
Proof.
  unfold lf in *.
  lf_constant 24; lf_context g; lf_finish.
Qed.

Lemma encoded_nk_bottom g a p0 :
  lf (NK_code g Bottom) p0 ->
  lf (NK_code g a) (rule_app 25 [(encode_context g); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 25; lf_context g; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_imp_intro g a b p0 :
  lf (NK_code (a :: g) b) p0 ->
  lf (NK_code g (Imp a b)) (rule_app 26 [(encode_context g); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 26; lf_context g; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_imp_elim g a b p0 p1 :
  lf (NK_code g (Imp a b)) p0 ->
  lf (NK_code g a) p1 ->
  lf (NK_code g b) (rule_app 27 [(encode_context g); (encode a); (encode b); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 27; lf_context g; lf_formula a; lf_formula b; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_nk_conj_intro g a b p0 p1 :
  lf (NK_code g a) p0 ->
  lf (NK_code g b) p1 ->
  lf (NK_code g (Conj a b)) (rule_app 28 [(encode_context g); (encode a); (encode b); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 28; lf_context g; lf_formula a; lf_formula b; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_nk_conj_left g a b p0 :
  lf (NK_code g (Conj a b)) p0 ->
  lf (NK_code g a) (rule_app 29 [(encode_context g); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 29; lf_context g; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_conj_right g a b p0 :
  lf (NK_code g (Conj a b)) p0 ->
  lf (NK_code g b) (rule_app 30 [(encode_context g); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 30; lf_context g; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_disj_left g a b p0 :
  lf (NK_code g a) p0 ->
  lf (NK_code g (Disj a b)) (rule_app 31 [(encode_context g); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 31; lf_context g; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_disj_right g a b p0 :
  lf (NK_code g b) p0 ->
  lf (NK_code g (Disj a b)) (rule_app 32 [(encode_context g); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 32; lf_context g; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_disj_elim g a b c p0 p1 p2 :
  lf (NK_code g (Disj a b)) p0 ->
  lf (NK_code (a :: g) c) p1 ->
  lf (NK_code (b :: g) c) p2 ->
  lf (NK_code g c) (rule_app 33 [(encode_context g); (encode a); (encode b); (encode c); p0; p1; p2]).
Proof.
  intros P0 P1 P2; unfold lf in *.
  lf_constant 33; lf_context g; lf_formula a; lf_formula b; lf_formula c; lf_argument P0; lf_argument P1; lf_argument P2; lf_finish.
Qed.

Lemma encoded_nk_neg_intro g a p0 :
  lf (NK_code (a :: g) Bottom) p0 ->
  lf (NK_code g (Neg a)) (rule_app 34 [(encode_context g); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 34; lf_context g; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_nk_neg_elim g a p0 p1 :
  lf (NK_code g (Neg a)) p0 ->
  lf (NK_code g a) p1 ->
  lf (NK_code g Bottom) (rule_app 35 [(encode_context g); (encode a); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 35; lf_context g; lf_formula a; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_nk_classical g a p0 :
  lf (NK_code (Neg a :: g) Bottom) p0 ->
  lf (NK_code g a) (rule_app 36 [(encode_context g); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 36; lf_context g; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_identity a :
  lf (LK_code [a] [a]) (rule_app 38 [(encode a)]).
Proof.
  unfold lf in *.
  lf_constant 38; lf_formula a; lf_finish.
Qed.

Lemma encoded_lk_bottom g d :
  lf (LK_code (Bottom :: g) d) (rule_app 39 [(encode_context g); (encode_context d)]).
Proof.
  unfold lf in *.
  lf_constant 39; lf_context g; lf_context d; lf_finish.
Qed.

Lemma encoded_lk_top g d :
  lf (LK_code g (Top :: d)) (rule_app 40 [(encode_context g); (encode_context d)]).
Proof.
  unfold lf in *.
  lf_constant 40; lf_context g; lf_context d; lf_finish.
Qed.

Lemma encoded_lk_weak_left g d a p0 :
  lf (LK_code g d) p0 ->
  lf (LK_code (a :: g) d) (rule_app 41 [(encode_context g); (encode_context d); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 41; lf_context g; lf_context d; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_weak_right g d a p0 :
  lf (LK_code g d) p0 ->
  lf (LK_code g (a :: d)) (rule_app 42 [(encode_context g); (encode_context d); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 42; lf_context g; lf_context d; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_contract_left g d a p0 :
  lf (LK_code (a :: a :: g) d) p0 ->
  lf (LK_code (a :: g) d) (rule_app 43 [(encode_context g); (encode_context d); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 43; lf_context g; lf_context d; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_contract_right g d a p0 :
  lf (LK_code g (a :: a :: d)) p0 ->
  lf (LK_code g (a :: d)) (rule_app 44 [(encode_context g); (encode_context d); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 44; lf_context g; lf_context d; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_exchange_left g h d p0 p1 :
  lf (permutation_type g h) p0 ->
  lf (LK_code g d) p1 ->
  lf (LK_code h d) (rule_app 45 [(encode_context g); (encode_context h); (encode_context d); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 45; lf_context g; lf_context h; lf_context d; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_lk_exchange_right g h d p0 p1 :
  lf (permutation_type d h) p0 ->
  lf (LK_code g d) p1 ->
  lf (LK_code g h) (rule_app 46 [(encode_context g); (encode_context h); (encode_context d); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 46; lf_context g; lf_context h; lf_context d; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_lk_imp_right g d a b p0 :
  lf (LK_code (a :: g) (b :: d)) p0 ->
  lf (LK_code g (Imp a b :: d)) (rule_app 47 [(encode_context g); (encode_context d); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 47; lf_context g; lf_context d; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_imp_left g d a b p0 p1 :
  lf (LK_code g (a :: d)) p0 ->
  lf (LK_code (b :: g) d) p1 ->
  lf (LK_code (Imp a b :: g) d) (rule_app 48 [(encode_context g); (encode_context d); (encode a); (encode b); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 48; lf_context g; lf_context d; lf_formula a; lf_formula b; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_lk_conj_left g d a b p0 :
  lf (LK_code (a :: b :: g) d) p0 ->
  lf (LK_code (Conj a b :: g) d) (rule_app 49 [(encode_context g); (encode_context d); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 49; lf_context g; lf_context d; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_conj_right g d a b p0 p1 :
  lf (LK_code g (a :: d)) p0 ->
  lf (LK_code g (b :: d)) p1 ->
  lf (LK_code g (Conj a b :: d)) (rule_app 50 [(encode_context g); (encode_context d); (encode a); (encode b); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 50; lf_context g; lf_context d; lf_formula a; lf_formula b; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_lk_disj_left g d a b p0 p1 :
  lf (LK_code (a :: g) d) p0 ->
  lf (LK_code (b :: g) d) p1 ->
  lf (LK_code (Disj a b :: g) d) (rule_app 51 [(encode_context g); (encode_context d); (encode a); (encode b); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 51; lf_context g; lf_context d; lf_formula a; lf_formula b; lf_argument P0; lf_argument P1; lf_finish.
Qed.

Lemma encoded_lk_disj_right g d a b p0 :
  lf (LK_code g (a :: b :: d)) p0 ->
  lf (LK_code g (Disj a b :: d)) (rule_app 52 [(encode_context g); (encode_context d); (encode a); (encode b); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 52; lf_context g; lf_context d; lf_formula a; lf_formula b; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_neg_left g d a p0 :
  lf (LK_code g (a :: d)) p0 ->
  lf (LK_code (Neg a :: g) d) (rule_app 53 [(encode_context g); (encode_context d); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 53; lf_context g; lf_context d; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_neg_right g d a p0 :
  lf (LK_code (a :: g) d) p0 ->
  lf (LK_code g (Neg a :: d)) (rule_app 54 [(encode_context g); (encode_context d); (encode a); p0]).
Proof.
  intros P0; unfold lf in *.
  lf_constant 54; lf_context g; lf_context d; lf_formula a; lf_argument P0; lf_finish.
Qed.

Lemma encoded_lk_cut g d a p0 p1 :
  lf (LK_code g (a :: d)) p0 ->
  lf (LK_code (a :: g) d) p1 ->
  lf (LK_code g d) (rule_app 55 [(encode_context g); (encode_context d); (encode a); p0; p1]).
Proof.
  intros P0 P1; unfold lf in *.
  lf_constant 55; lf_context g; lf_context d; lf_formula a; lf_argument P0; lf_argument P1; lf_finish.
Qed.

(** Prop-valued source derivations give existence of closed LF evidence;
    no elimination of a Rocq proof into computational data is assumed. *)
Theorem membership_has_lf_evidence a g :
  In a g -> exists p, lf (member_type a g) p.
Proof.
  induction g as [|b g IH]; simpl; [contradiction|].
  intros [E|H].
  - subst b; eexists; apply encoded_in_here.
  - destruct (IH H) as [p P]; eexists; apply encoded_in_there; exact P.
Qed.

Theorem permutation_has_lf_evidence g h :
  Permutation g h -> exists p, lf (permutation_type g h) p.
Proof.
  intros H; induction H.
  - eexists; apply encoded_perm_nil.
  - destruct IHPermutation as [p P]; eexists; apply encoded_perm_cons; exact P.
  - eexists; apply encoded_perm_swap.
  - destruct IHPermutation1 as [p P], IHPermutation2 as [q Q].
    eexists; apply encoded_perm_trans; eassumption.
Qed.

Theorem NK_has_lf_derivation g a :
  NK g a -> exists p, lf (NK_code g a) p.
Proof.
  intros H; induction H;
    repeat match goal with
    | IH : exists p, lf _ p |- _ => destruct IH as [? ?]
    end.
  - destruct (membership_has_lf_evidence _ _ H) as [p P].
    eexists; apply encoded_nk_assume; exact P.
  - eexists; apply encoded_nk_top.
  - eexists; eapply encoded_nk_bottom; eassumption.
  - eexists; eapply encoded_nk_imp_intro; eassumption.
  - eexists; eapply encoded_nk_imp_elim; eassumption.
  - eexists; eapply encoded_nk_conj_intro; eassumption.
  - eexists; eapply encoded_nk_conj_left; eassumption.
  - eexists; eapply encoded_nk_conj_right; eassumption.
  - eexists; eapply encoded_nk_disj_left; eassumption.
  - eexists; eapply encoded_nk_disj_right; eassumption.
  - eexists; eapply encoded_nk_disj_elim; eassumption.
  - eexists; eapply encoded_nk_neg_intro; eassumption.
  - eexists; eapply encoded_nk_neg_elim; eassumption.
  - eexists; eapply encoded_nk_classical; eassumption.
Qed.

Theorem LK_has_lf_derivation g d :
  LK g d -> exists p, lf (LK_code g d) p.
Proof.
  intros H; induction H;
    repeat match goal with
    | IH : exists p, lf _ p |- _ => destruct IH as [? ?]
    end.
  - eexists; apply encoded_lk_identity.
  - eexists; apply encoded_lk_bottom.
  - eexists; apply encoded_lk_top.
  - eexists; eapply encoded_lk_weak_left; eassumption.
  - eexists; eapply encoded_lk_weak_right; eassumption.
  - eexists; eapply encoded_lk_contract_left; eassumption.
  - eexists; eapply encoded_lk_contract_right; eassumption.
  - destruct (permutation_has_lf_evidence _ _ H) as [p P].
    eexists; eapply encoded_lk_exchange_left; eassumption.
  - destruct (permutation_has_lf_evidence _ _ H) as [p P].
    eexists; eapply encoded_lk_exchange_right; eassumption.
  - eexists; eapply encoded_lk_imp_right; eassumption.
  - eexists; eapply encoded_lk_imp_left; eassumption.
  - eexists; eapply encoded_lk_conj_left; eassumption.
  - eexists; eapply encoded_lk_conj_right; eassumption.
  - eexists; eapply encoded_lk_disj_left; eassumption.
  - eexists; eapply encoded_lk_disj_right; eassumption.
  - eexists; eapply encoded_lk_neg_left; eassumption.
  - eexists; eapply encoded_lk_neg_right; eassumption.
  - eexists; eapply encoded_lk_cut; eassumption.
Qed.

(** The evidence can be installed as a proof declaration without adding any
    assumptions. This is declarative validity, not bounded checker acceptance. *)
Corollary NK_has_valid_pa_proof g a : NK g a ->
  exists p, valid_program fixed_signature [Prove (NK_code g a) p]
    (fixed_signature ++ [NK_code g a]).
Proof.
  intros H; destruct (NK_has_lf_derivation _ _ H) as [p P]; exists p.
  apply vp_cons; [|apply vp_nil].
  split; [exists tType; split|]; simpl.
  - apply NK_code_is_type.
  - left; reflexivity.
  - exact P.
Qed.
Corollary LK_has_valid_pa_proof g d : LK g d ->
  exists p, valid_program fixed_signature [Prove (LK_code g d) p]
    (fixed_signature ++ [LK_code g d]).
Proof.
  intros H; destruct (LK_has_lf_derivation _ _ H) as [p P]; exists p.
  apply vp_cons; [|apply vp_nil].
  split; [exists tType; split|]; simpl.
  - apply LK_code_is_type.
  - left; reflexivity.
  - exact P.
Qed.

Print Assumptions membership_has_lf_evidence.
Print Assumptions permutation_has_lf_evidence.
Print Assumptions NK_has_lf_derivation.
Print Assumptions LK_has_lf_derivation.
Print Assumptions NK_has_valid_pa_proof.
Print Assumptions LK_has_valid_pa_proof.

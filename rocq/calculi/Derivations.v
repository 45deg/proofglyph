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

(** Apply a checked signature entry to encoded data, then to the available
    LF evidence. Every application still constructs a kernel-checked ty_app. *)
Ltac lf_rule k args :=
  unfold lf in *; lf_constant k;
  let rec data xs := lazymatch xs with
    | [] => idtac
    | encode ?a :: ?rest => lf_formula a; data rest
    | encode_context ?g :: ?rest => lf_context g; data rest
    end in data args;
  unfold member_type, permutation_type, NK_code, LK_code, nk_type, lk_type,
    code_binary in *; cbn [encode encode_context] in *; unfold code_binary in *;
  repeat match goal with
  | F : typing fixed_signature [] _ (tPi ?a _) |- _ =>
    match goal with X : typing fixed_signature [] _ a |- _ => lf_argument X end
  end;
  match goal with F : typing fixed_signature [] ?t _ |- _ => exists t; lf_finish end.

(** Prop-valued source derivations give existence of closed LF evidence;
    no elimination of a Rocq proof into computational data is assumed. *)
Theorem membership_has_lf_evidence a g :
  In a g -> exists p, lf (member_type a g) p.
Proof.
  induction g as [|b g IH]; simpl; [contradiction|].
  intros [E|H].
  - subst b; lf_rule 15 [encode a; encode_context g].
  - destruct (IH H) as [p P]; lf_rule 16 [encode a; encode b; encode_context g].
Qed.

Theorem permutation_has_lf_evidence g h :
  Permutation g h -> exists p, lf (permutation_type g h) p.
Proof.
  intros H; induction H as [|a g h PERM IH|a b g|g h d GH IHGH HD IHHD].
  - lf_rule 18 (@nil term).
  - destruct IH as [p P]; lf_rule 19 [encode a; encode_context g; encode_context h].
  - lf_rule 20 [encode b; encode a; encode_context g].
  - destruct IHGH as [p P], IHHD as [q Q].
    lf_rule 21 [encode_context g; encode_context h; encode_context d].
Qed.

Theorem NK_has_lf_derivation g a :
  NK g a -> exists p, lf (NK_code g a) p.
Proof.
  intros H; induction H;
    repeat match goal with
    | IH : exists p, lf _ p |- _ => destruct IH as [? ?]
    end.
  - destruct (membership_has_lf_evidence _ _ H) as [p P].
    lf_rule 23 [encode_context g; encode a].
  - lf_rule 24 [encode_context g].
  - lf_rule 25 [encode_context g; encode a].
  - lf_rule 26 [encode_context g; encode a; encode b].
  - lf_rule 27 [encode_context g; encode a; encode b].
  - lf_rule 28 [encode_context g; encode a; encode b].
  - lf_rule 29 [encode_context g; encode a; encode b].
  - lf_rule 30 [encode_context g; encode a; encode b].
  - lf_rule 31 [encode_context g; encode a; encode b].
  - lf_rule 32 [encode_context g; encode a; encode b].
  - lf_rule 33 [encode_context g; encode a; encode b; encode c].
  - lf_rule 34 [encode_context g; encode a].
  - lf_rule 35 [encode_context g; encode a].
  - lf_rule 36 [encode_context g; encode a].
Qed.

Theorem LK_has_lf_derivation g d :
  LK g d -> exists p, lf (LK_code g d) p.
Proof.
  intros H; induction H;
    repeat match goal with
    | IH : exists p, lf _ p |- _ => destruct IH as [? ?]
    end.
  - lf_rule 38 [encode a].
  - lf_rule 39 [encode_context g; encode_context d].
  - lf_rule 40 [encode_context g; encode_context d].
  - lf_rule 41 [encode_context g; encode_context d; encode a].
  - lf_rule 42 [encode_context g; encode_context d; encode a].
  - lf_rule 43 [encode_context g; encode_context d; encode a].
  - lf_rule 44 [encode_context g; encode_context d; encode a].
  - destruct (permutation_has_lf_evidence _ _ H) as [p P].
    lf_rule 45 [encode_context g; encode_context h; encode_context d].
  - destruct (permutation_has_lf_evidence _ _ H) as [p P].
    lf_rule 46 [encode_context g; encode_context h; encode_context d].
  - lf_rule 47 [encode_context g; encode_context d; encode a; encode b].
  - lf_rule 48 [encode_context g; encode_context d; encode a; encode b].
  - lf_rule 49 [encode_context g; encode_context d; encode a; encode b].
  - lf_rule 50 [encode_context g; encode_context d; encode a; encode b].
  - lf_rule 51 [encode_context g; encode_context d; encode a; encode b].
  - lf_rule 52 [encode_context g; encode_context d; encode a; encode b].
  - lf_rule 53 [encode_context g; encode_context d; encode a].
  - lf_rule 54 [encode_context g; encode_context d; encode a].
  - lf_rule 55 [encode_context g; encode_context d; encode a].
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

From Stdlib Require Import List PeanoNat Bool Lia.
From Proofglyph.Zfc Require Import Formula.

Definition up (rho : nat -> nat) n := match n with 0 => 0 | S k => S (rho k) end.
Fixpoint rename (rho : nat -> nat) p := match p with
| Bot => Bot
| Equal x y => Equal (rho x) (rho y)
| Member x y => Member (rho x) (rho y)
| Implies p q => Implies (rename rho p) (rename rho q)
| Forall p => Forall (rename (up rho) p)
end.

Lemma rename_scoped p : forall n m rho,
  (forall i, i < n -> rho i < m) -> scoped n p = true -> scoped m (rename rho p) = true.
Proof.
  induction p; intros n0 m rho R H; cbn in *; try reflexivity.
  - apply andb_true_iff in H as [X Y]; apply andb_true_iff; split;
      apply Nat.ltb_lt; apply R; apply Nat.ltb_lt; assumption.
  - apply andb_true_iff in H as [X Y]; apply andb_true_iff; split;
      apply Nat.ltb_lt; apply R; apply Nat.ltb_lt; assumption.
  - apply andb_true_iff in H as [P Q]; apply andb_true_iff; split; eauto.
  - eapply IHp; [|exact H]. intros [|i] L; cbn [up]; [lia|].
    specialize (R i ltac:(lia)); lia.
Qed.

Fixpoint close n p := match n with 0 => p | S n => Forall (close n p) end.
Lemma scoped_close n p : forall d, scoped d (close n p) = scoped (n + d) p.
Proof.
  induction n; intros d; cbn; [reflexivity|]. rewrite IHn.
  replace (n + S d) with (S (n + d)) by lia; reflexivity.
Qed.
Lemma close_sentence n p : scoped n p = true -> sentence (close n p).
Proof. unfold sentence; rewrite scoped_close, Nat.add_0_r; auto. Qed.

Definition union := Forall (Exists (Forall
  (Iff (Member 0 1) (Exists (And (Member 0 3) (Member 1 0)))))).
Definition power_set := Forall (Exists (Forall
  (Iff (Member 0 1) (Forall (Implies (Member 0 1) (Member 0 3)))))).
Definition infinity := Exists (And
  (Exists (And (Member 0 1) (Forall (Neg (Member 0 1)))))
  (Forall (Implies (Member 0 1) (Exists (And (Member 0 2)
    (Forall (Iff (Member 0 1) (Or (Member 0 2) (Equal 0 2))))))))).
Definition foundation := Forall (Implies (Exists (Member 0 1))
  (Exists (And (Member 0 1) (Forall (Neg (And (Member 0 1) (Member 0 2))))))).

(** Choice-set form of AC: every pairwise-disjoint family of nonempty sets
    has a set meeting each member in exactly one element. *)
Definition choice := Forall (Implies
  (And
    (Forall (Implies (Member 0 1) (Exists (Member 0 1))))
    (Forall (Forall (Implies
      (And (Member 1 2) (And (Member 0 2) (Neg (Equal 1 0))))
      (Forall (Neg (And (Member 0 2) (Member 0 1))))))))
  (Exists (Forall (Implies (Member 0 2) (Exists
    (And (And (Member 0 1) (Member 0 2))
      (Forall (Implies (And (Member 0 2) (Member 0 3)) (Equal 0 1))))))))).

(** phi has x at index 0, then n parameters. Under [x,b,a,parameters],
    preserve x and shift parameters by two. b cannot occur freely in phi. *)
Definition sep_ren i := match i with 0 => 0 | S k => S (S (S k)) end.
Definition separation n phi := close n (Forall (Exists (Forall
  (Iff (Member 0 1) (And (Member 0 2) (rename sep_ren phi)))))).

(** theta has y at 0, x at 1, then n parameters. *)
Definition rep_value i := match i with 0 => 0 | 1 => 1 | S (S k) => 3 + k end.
Definition rep_unique i := match i with 0 => 0 | 1 => 2 | S (S k) => 4 + k end.
Definition rep_image i := match i with 0 => 1 | 1 => 0 | S (S k) => 4 + k end.
Definition replacement n theta := close n (Forall (Implies
  (Forall (Implies (Member 0 1) (Exists
    (And (rename rep_value theta)
      (Forall (Implies (rename rep_unique theta) (Equal 0 1)))))))
  (Exists (Forall (Iff (Member 0 1)
    (Exists (And (Member 0 3) (rename rep_image theta)))))))).

Example union_closed : sentence union. Proof. reflexivity. Qed.
Example power_set_closed : sentence power_set. Proof. reflexivity. Qed.
Example infinity_closed : sentence infinity. Proof. reflexivity. Qed.
Example foundation_closed : sentence foundation. Proof. reflexivity. Qed.
Example choice_closed : sentence choice. Proof. reflexivity. Qed.

Ltac split_scopes :=
  cbn [scoped Iff And Or Neg Exists];
  repeat rewrite andb_true_iff; repeat split; try reflexivity.

Theorem separation_closed n phi : scoped (S n) phi = true -> sentence (separation n phi).
Proof.
  intros H; unfold separation; apply close_sentence; split_scopes.
  all: eapply rename_scoped; [|exact H]; intros [|i] L; cbn [sep_ren]; lia.
Qed.

Theorem replacement_closed n theta : scoped (S (S n)) theta = true ->
  sentence (replacement n theta).
Proof.
  intros H; unfold replacement; apply close_sentence; split_scopes;
    eapply rename_scoped; try exact H;
    intros [|[|i]] L; cbn [rep_value rep_unique rep_image]; lia.
Qed.

(** This is an inductive syntactic axiom predicate, NOT a Rocq assumption
    asserting the truth or consistency of set theory. *)
Inductive zfc_axiom : formula -> Prop :=
| ax_extensionality : zfc_axiom extensionality
| ax_empty : zfc_axiom empty_set
| ax_pairing : zfc_axiom pairing
| ax_union : zfc_axiom union
| ax_power : zfc_axiom power_set
| ax_infinity : zfc_axiom infinity
| ax_foundation : zfc_axiom foundation
| ax_choice : zfc_axiom choice
| ax_separation : forall n phi, scoped (S n) phi = true -> zfc_axiom (separation n phi)
| ax_replacement : forall n theta, scoped (S (S n)) theta = true -> zfc_axiom (replacement n theta).

Theorem all_axioms_closed p : zfc_axiom p -> sentence p.
Proof.
  intros H; destruct H; try reflexivity;
    [apply separation_closed|apply replacement_closed]; assumption.
Qed.

Example separation_parameter_guard : scoped 1 (Member 0 1) = false.
Proof. reflexivity. Qed.
Example separation_with_parameter : sentence (separation 1 (Member 0 1)).
Proof. apply separation_closed; reflexivity. Qed.
Example replacement_identity : sentence (replacement 0 (Equal 0 1)).
Proof. apply replacement_closed; reflexivity. Qed.
Example replacement_parameter : sentence (replacement 1 (Member 0 2)).
Proof. apply replacement_closed; reflexivity. Qed.
Example separation_binder_preserved :
  rename sep_ren (Forall (Member 0 2)) = Forall (Member 0 4).
Proof. reflexivity. Qed.

Print Assumptions separation_closed.
Print Assumptions replacement_closed.
Print Assumptions all_axioms_closed.

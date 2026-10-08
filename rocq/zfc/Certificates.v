From Stdlib Require Import List.
From Tinyprover.Zfc Require Import Formula Axioms Deduction.
Import ListNotations.

(** First-order relational certificates for the computations in the fixed LF
    prelude. These theorems concern certificate syntax; LF adequacy is separate. *)
Inductive index_map :=
| ShiftMap | UnbindMap (x : nat) | UpMap (r : index_map)
| SepMap | ValueMap | UniqueMap | ImageMap.
Fixpoint map_function r := match r with
| ShiftMap => S | UnbindMap x => unbind x | UpMap r => up (map_function r)
| SepMap => sep_ren | ValueMap => rep_value
| UniqueMap => rep_unique | ImageMap => rep_image
end.

Inductive maps : index_map -> nat -> nat -> Prop :=
| cm_shift : forall i, maps ShiftMap i (S i)
| cm_unbind_zero : forall x, maps (UnbindMap x) 0 x
| cm_unbind_succ : forall x i, maps (UnbindMap x) (S i) i
| cm_up_zero : forall r, maps (UpMap r) 0 0
| cm_up_succ : forall r i j, maps r i j -> maps (UpMap r) (S i) (S j)
| cm_sep_zero : maps SepMap 0 0
| cm_sep_succ : forall i, maps SepMap (S i) (S (S (S i)))
| cm_value_zero : maps ValueMap 0 0
| cm_value_one : maps ValueMap 1 1
| cm_value_tail : forall i, maps ValueMap (S (S i)) (S (S (S i)))
| cm_unique_zero : maps UniqueMap 0 0
| cm_unique_one : maps UniqueMap 1 2
| cm_unique_tail : forall i, maps UniqueMap (S (S i)) (S (S (S (S i))))
| cm_image_zero : maps ImageMap 0 1
| cm_image_one : maps ImageMap 1 0
| cm_image_tail : forall i, maps ImageMap (S (S i)) (S (S (S (S i)))).

Lemma maps_sound r i j : maps r i j -> j = map_function r i.
Proof. intros H; induction H; simpl in *; congruence. Qed.
Lemma maps_complete r i : maps r i (map_function r i).
Proof.
  revert i; induction r; intros [|[|i]]; cbn [map_function unbind up sep_ren
    rep_value rep_unique rep_image]; simpl; constructor; auto.
Qed.

Inductive renames : index_map -> formula -> formula -> Prop :=
| cr_bottom : forall r, renames r Bot Bot
| cr_equal : forall r x y u v, maps r x u -> maps r y v ->
    renames r (Equal x y) (Equal u v)
| cr_member : forall r x y u v, maps r x u -> maps r y v ->
    renames r (Member x y) (Member u v)
| cr_imp : forall r p q u v, renames r p u -> renames r q v ->
    renames r (Implies p q) (Implies u v)
| cr_all : forall r p q, renames (UpMap r) p q -> renames r (Forall p) (Forall q).

Lemma renames_sound r p q : renames r p q -> q = rename (map_function r) p.
Proof.
  intros H; induction H; cbn [rename]; f_equal; eauto using maps_sound.
Qed.
Lemma renames_complete r p : renames r p (rename (map_function r) p).
Proof.
  revert r; induction p; intros r; cbn [rename]; constructor; auto using maps_complete.
Qed.

Inductive closes : nat -> formula -> formula -> Prop :=
| cc_zero : forall p, closes 0 p p
| cc_succ : forall n p q, closes n p q -> closes (S n) p (Forall q).
Lemma closes_sound n p q : closes n p q -> q = close n p.
Proof. intros H; induction H; cbn [close]; congruence. Qed.
Lemma closes_complete n p : closes n p (close n p).
Proof. induction n; cbn [close]; constructor; auto. Qed.

Inductive lifts : list formula -> list formula -> Prop :=
| cl_nil : lifts [] []
| cl_cons : forall p q g h, renames ShiftMap p q -> lifts g h -> lifts (p :: g) (q :: h).
Lemma lifts_sound g h : lifts g h -> h = lift_hypotheses g.
Proof.
  intros H; induction H; cbn [lift_hypotheses]; [reflexivity|].
  rewrite (renames_sound _ _ _ H), IHlifts; reflexivity.
Qed.
Lemma lifts_complete g : lifts g (lift_hypotheses g).
Proof. induction g; constructor; auto using renames_complete. Qed.

Definition separation_body renamed := Forall (Exists (Forall
  (Iff (Member 0 1) (And (Member 0 2) renamed)))).
Definition replacement_body value unique image := Forall (Implies
  (Forall (Implies (Member 0 1) (Exists
    (And value (Forall (Implies unique (Equal 0 1)))))))
  (Exists (Forall (Iff (Member 0 1) (Exists (And (Member 0 3) image)))))).

Inductive axiom_certificate : formula -> Prop :=
| ca_extensionality : axiom_certificate extensionality
| ca_empty : axiom_certificate empty_set
| ca_pairing : axiom_certificate pairing
| ca_union : axiom_certificate union
| ca_power : axiom_certificate power_set
| ca_infinity : axiom_certificate infinity
| ca_foundation : axiom_certificate foundation
| ca_choice : axiom_certificate choice
| ca_separation : forall n phi renamed result,
    scoped (S n) phi = true -> renames SepMap phi renamed ->
    closes n (separation_body renamed) result -> axiom_certificate result
| ca_replacement : forall n theta value unique image result,
    scoped (S (S n)) theta = true ->
    renames ValueMap theta value -> renames UniqueMap theta unique ->
    renames ImageMap theta image ->
    closes n (replacement_body value unique image) result -> axiom_certificate result.

Theorem axiom_certificate_sound p : axiom_certificate p -> zfc_axiom p.
Proof.
  intros H; destruct H; try constructor.
  - rewrite (closes_sound _ _ _ H1), (renames_sound _ _ _ H0).
    change (zfc_axiom (separation n phi)); constructor; exact H.
  - rewrite (closes_sound _ _ _ H3), (renames_sound _ _ _ H0),
      (renames_sound _ _ _ H1), (renames_sound _ _ _ H2).
    change (zfc_axiom (replacement n theta)); constructor; exact H.
Qed.
Theorem axiom_certificate_complete p : zfc_axiom p -> axiom_certificate p.
Proof.
  intros H; destruct H; try constructor.
  - unfold separation; eapply ca_separation; eauto using renames_complete, closes_complete.
  - unfold replacement; eapply ca_replacement; eauto using renames_complete, closes_complete.
Qed.
Corollary axiom_certificate_iff p : axiom_certificate p <-> zfc_axiom p.
Proof. split; auto using axiom_certificate_sound, axiom_certificate_complete. Qed.

Inductive proof_certificate : nat -> list formula -> formula -> Prop :=
| cp_assume : forall n g p, scoped n p = true -> In p g -> proof_certificate n g p
| cp_axiom : forall n g p, axiom_certificate p -> proof_certificate n g p
| cp_imp_intro : forall n g p q, scoped n p = true ->
    proof_certificate n (p :: g) q -> proof_certificate n g (Implies p q)
| cp_imp_elim : forall n g p q, proof_certificate n g (Implies p q) ->
    proof_certificate n g p -> proof_certificate n g q
| cp_false : forall n g p, scoped n p = true -> proof_certificate n g Bot -> proof_certificate n g p
| cp_classical : forall n g p, scoped n p = true ->
    proof_certificate n (Neg p :: g) Bot -> proof_certificate n g p
| cp_all_intro : forall n g h p, lifts g h ->
    proof_certificate (S n) h p -> proof_certificate n g (Forall p)
| cp_all_elim : forall n g p q x, x < n -> renames (UnbindMap x) p q ->
    proof_certificate n g (Forall p) -> proof_certificate n g q
| cp_eq_refl : forall n g x, x < n -> proof_certificate n g (Equal x x)
| cp_eq_subst : forall n g p px py x y, scoped (S n) p = true -> x < n -> y < n ->
    renames (UnbindMap x) p px -> renames (UnbindMap y) p py ->
    proof_certificate n g (Equal x y) -> proof_certificate n g px -> proof_certificate n g py.

Theorem proof_certificate_sound n g p : proof_certificate n g p -> derives n g p.
Proof.
  intros H; induction H; eauto using nd_assume, nd_axiom, axiom_certificate_sound,
    nd_imp_intro, nd_imp_elim, nd_false, nd_classical, nd_eq_refl.
  - rewrite (lifts_sound _ _ H) in IHproof_certificate; apply nd_all_intro; exact IHproof_certificate.
  - rewrite (renames_sound _ _ _ H0); apply nd_all_elim; assumption.
  - rewrite (renames_sound _ _ _ H2) in IHproof_certificate2.
    rewrite (renames_sound _ _ _ H3).
    change (derives n g (instantiate_formula y p)).
    eapply nd_eq_subst with (p := p) (x := x) (y := y); eauto.
Qed.
Theorem proof_certificate_complete n g p : derives n g p -> proof_certificate n g p.
Proof.
  intros H; induction H; eauto using cp_assume, cp_axiom, axiom_certificate_complete,
    cp_imp_intro, cp_imp_elim, cp_false, cp_classical, cp_eq_refl.
  - eapply cp_all_intro; eauto using lifts_complete.
  - unfold instantiate_formula; eapply cp_all_elim; eauto using renames_complete.
  - unfold instantiate_formula in *; eapply cp_eq_subst with (p := p) (x := x) (y := y); eauto using renames_complete.
Qed.
Corollary proof_certificate_iff p : proof_certificate 0 [] p <-> ZFC_proves p.
Proof. unfold ZFC_proves; split; auto using proof_certificate_sound, proof_certificate_complete. Qed.

Print Assumptions axiom_certificate_iff.
Print Assumptions proof_certificate_iff.

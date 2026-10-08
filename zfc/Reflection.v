From Stdlib Require Import List PeanoNat Bool Lia.
From Rocq4pa Require Import Syntax Program Kernel Substitution WellFormed TypingSubstitution
  Checker Evaluation Confluence Preservation TypedNormalization.
From Zfc Require Import Formula Axioms Deduction Encoding Certificates Specification.
From ZfcDeep Require Import Artifact DeepVerification Translation GroundAdequacy.
Import ListNotations.

Lemma index_code_injective n m : encode_index n = encode_index m -> n = m.
Proof. intros H; apply (f_equal decode_index) in H; rewrite !index_roundtrip in H; congruence. Qed.
Fixpoint decode_map t := match t with
| tConst 19 => Some ShiftMap
| tApp (tConst 20) x => option_map UnbindMap (decode_index x)
| tApp (tConst 21) r => option_map UpMap (decode_map r)
| tConst 22 => Some SepMap | tConst 23 => Some ValueMap
| tConst 24 => Some UniqueMap | tConst 25 => Some ImageMap | _ => None end.
Lemma map_roundtrip r : decode_map (encode_map r) = Some r.
Proof. induction r; cbn; rewrite ?index_roundtrip, ?IHr; reflexivity. Qed.
Lemma map_code_injective r s : encode_map r = encode_map s -> r = s.
Proof. intros H; apply (f_equal decode_map) in H; rewrite !map_roundtrip in H; congruence. Qed.
Fixpoint decode_context t := match t with
| tConst 53 => Some []
| tApp (tApp (tConst 54) p) g => pair_options cons (decode p) (decode_context g)
| _ => None end.
Lemma context_roundtrip g : decode_context (encode_context g) = Some g.
Proof. induction g; cbn; rewrite ?formula_roundtrip, ?IHg; reflexivity. Qed.
Lemma context_code_injective g h : encode_context g = encode_context h -> g = h.
Proof. intros H; apply (f_equal decode_context) in H; rewrite !context_roundtrip in H; congruence. Qed.

Inductive atomic_meaning : term -> term -> Prop :=
| am_type : forall t, atomic_meaning tType t
| am_index : forall n, atomic_meaning index_type (encode_index n)
| am_formula : forall p, atomic_meaning formula_type (encode p)
| am_map : forall r, atomic_meaning (tConst 18) (encode_map r)
| am_context : forall g, atomic_meaning (tConst 52) (encode_context g)
| am_lt : forall x n t, x < n -> atomic_meaning (lt_type x n) t
| am_scope : forall n p t, scoped n p = true -> atomic_meaning (scoped_type (encode_index n) (encode p)) t
| am_maps : forall r i j t, maps r i j -> atomic_meaning (maps_type r i j) t
| am_rename : forall r p q t, renames r p q -> atomic_meaning (rename_type (encode_map r) (encode p) (encode q)) t
| am_close : forall n p q t, closes n p q -> atomic_meaning (close_type (encode_index n) (encode p) (encode q)) t
| am_in : forall p g t, In p g -> atomic_meaning (in_type p g) t
| am_lifts : forall g h t, lifts g h -> atomic_meaning (lifts_type g h) t
| am_axiom : forall p t, axiom_certificate p -> atomic_meaning (zax (encode p)) t
| am_proof : forall n g p t, proof_certificate n g p -> atomic_meaning (derives_type n g p) t.

Fixpoint pi_count a := match a with tPi _ b => S (pi_count b) | _ => 0 end.
Fixpoint realizes fuel a t : Prop := match a with
| tPi dom body => match fuel with
  | 0 => False
  | S fuel => forall x, ground x -> atomic_meaning dom x -> realizes fuel (instantiate body x) (tApp t x)
  end
| _ => atomic_meaning a t
end.
Lemma flat_pi_count t : flat t -> pi_count t = 0.
Proof. intros H; inversion H; reflexivity. Qed.
Lemma flat_realizes fuel a t : flat a -> realizes fuel a t <-> atomic_meaning a t.
Proof. intros H; destruct fuel; inversion H; reflexivity. Qed.
Lemma pi_count_subst a : first_order_type a -> forall d x, ground x -> pi_count (subst d x a) = pi_count a.
Proof.
  intros H; induction H; intros d x X; cbn [subst pi_count].
  - rewrite (flat_pi_count _ (flat_subst _ H _ _ X)), (flat_pi_count _ H); reflexivity.
  - reflexivity.
  - f_equal; auto.
Qed.

Fixpoint flatb t := match t with tVar _ | tConst _ => true | tApp f x => flatb f && flatb x | _ => false end.
Fixpoint first_orderb t := match t with
| tType => true | tPi a b => flatb a && first_orderb b | _ => flatb t end.
Lemma flatb_sound t : flatb t = true -> flat t.
Proof. induction t; cbn; intros H; try discriminate; try constructor; apply andb_true_iff in H as [F X]; auto. Qed.
Lemma first_orderb_sound t : first_orderb t = true -> first_order_type t.
Proof.
  induction t; cbn; intros H; try solve [apply fo_atom; apply flatb_sound; exact H].
  - apply fo_type.
  - apply andb_true_iff in H as [A B]; apply fo_pi; auto using flatb_sound.
Qed.
Example signature_first_order_computed : forallb first_orderb zfc_signature = true.
Proof. vm_compute; reflexivity. Qed.
Lemma zfc_signature_first_order k a : nth_error zfc_signature k = Some a -> first_order_type a.
Proof.
  intros K; apply first_orderb_sound.
  pose proof signature_first_order_computed as F.
  apply forallb_forall with (x := a) in F;
    [exact F|eapply nth_error_In; exact K].
Qed.
Lemma ground_type_first_order t a : ground_typing zfc_signature t a -> first_order_type a.
Proof.
  intros H; induction H.
  - eapply zfc_signature_first_order; exact H.
  - inversion IHground_typing1; subst; try match goal with H : flat (tPi _ _) |- _ => inversion H end.
    apply first_order_subst; [assumption|eapply ground_typing_ground; exact H0].
Qed.

Ltac code_equalities :=
  repeat match goal with
  | H : encode_index _ = encode_index _ |- _ => apply index_code_injective in H; subst
  | H : encode _ = encode _ |- _ => apply encode_injective in H; subst
  | H : encode_map _ = encode_map _ |- _ => apply map_code_injective in H; subst
  | H : encode_context _ = encode_context _ |- _ => apply context_code_injective in H; subst
  end.
Ltac invert_meaning :=
  match goal with H : atomic_meaning _ _ |- _ => inversion H; clear H; subst; code_equalities end.
#[local] Hint Rewrite subst_index subst_formula subst_map subst_context
  shift_index_code shift_formula_code shift_map_code shift_context_code : reflection_codes.
Ltac reduce_reflection :=
  repeat (progress (cbn [realizes pi_count instantiate subst shift Nat.eqb Nat.ltb Nat.leb Nat.pred Nat.add];
    autorewrite with reflection_codes)).

Ltac read_index t :=
  lazymatch t with
  | encode_index ?n => constr:(n)
  | tConst 1 => constr:(0)
  | tApp (tConst 2) ?x => let n := read_index x in constr:(S n)
  end.
Ltac read_formula t :=
  lazymatch t with
  | encode ?p => constr:(p)
  | tConst 4 => constr:(Bot)
  | tApp (tApp (tConst 5) ?x) ?y => let i := read_index x in let j := read_index y in constr:(Equal i j)
  | tApp (tApp (tConst 6) ?x) ?y => let i := read_index x in let j := read_index y in constr:(Member i j)
  | tApp (tApp (tConst 7) ?x) ?y => let p := read_formula x in let q := read_formula y in constr:(Implies p q)
  | tApp (tConst 8) ?x => let p := read_formula x in constr:(Formula.Forall p)
  end.
Ltac read_map t :=
  lazymatch t with
  | encode_map ?r => constr:(r)
  | tConst 19 => constr:(ShiftMap)
  | tConst 22 => constr:(SepMap)
  | tConst 23 => constr:(ValueMap)
  | tConst 24 => constr:(UniqueMap)
  | tConst 25 => constr:(ImageMap)
  | tApp (tConst 20) ?x => let n := read_index x in constr:(UnbindMap n)
  | tApp (tConst 21) ?x => let r := read_map x in constr:(UpMap r)
  end.
Ltac read_context t :=
  lazymatch t with
  | encode_context ?g => constr:(g)
  | tConst 53 => constr:(@nil formula)
  | tApp (tApp (tConst 54) ?x) ?y => let p := read_formula x in let g := read_context y in constr:(p :: g)
  end.
Ltac code_equalities ::=
  repeat first [
    match goal with H : encode_index ?n = ?raw |- _ =>
      let m := read_index raw in change (encode_index n = encode_index m) in H;
      apply index_code_injective in H; subst end
  | match goal with H : encode ?p = ?raw |- _ =>
      let q := read_formula raw in change (encode p = encode q) in H;
      apply encode_injective in H; subst end
  | match goal with H : encode_map ?r = ?raw |- _ =>
      let r0 := read_map raw in change (encode_map r = encode_map r0) in H;
      apply map_code_injective in H; subst end
  | match goal with H : encode_context ?g = ?raw |- _ =>
      let g0 := read_context raw in change (encode_context g = encode_context g0) in H;
      apply context_code_injective in H; subst end
  ].
Ltac head_index t := lazymatch t with tConst ?k => constr:(k) | tApp ?f _ => head_index f end.
Ltac choose_rule t :=
  let k := head_index t in lazymatch k with
  | 27 => eapply cm_shift
  | 28 => eapply cm_unbind_zero
  | 29 => eapply cm_unbind_succ
  | 30 => eapply cm_up_zero
  | 31 => eapply cm_up_succ
  | 32 => eapply cm_sep_zero
  | 33 => eapply cm_sep_succ
  | 34 => eapply cm_value_zero
  | 35 => eapply cm_value_one
  | 36 => eapply cm_value_tail
  | 37 => eapply cm_unique_zero
  | 38 => eapply cm_unique_one
  | 39 => eapply cm_unique_tail
  | 40 => eapply cm_image_zero
  | 41 => eapply cm_image_one
  | 42 => eapply cm_image_tail
  | 44 => eapply cr_bottom
  | 45 => eapply cr_equal
  | 46 => eapply cr_member
  | 47 => eapply cr_imp
  | 48 => eapply cr_all
  | 50 => eapply cc_zero
  | 51 => eapply cc_succ
  | 59 => eapply cl_nil
  | 60 => eapply cl_cons
  | 62 => eapply ca_extensionality
  | 63 => eapply ca_empty
  | 64 => eapply ca_pairing
  | 65 => eapply ca_union
  | 66 => eapply ca_power
  | 67 => eapply ca_infinity
  | 68 => eapply ca_foundation
  | 69 => eapply ca_choice
  | 70 => eapply ca_separation
  | 71 => eapply ca_replacement
  | 73 => eapply cp_assume
  | 74 => eapply cp_axiom
  | 75 => eapply cp_imp_intro
  | 76 => eapply cp_imp_elim
  | 77 => eapply cp_false
  | 78 => eapply cp_classical
  | 79 => eapply cp_all_intro
  | 80 => eapply cp_all_elim
  | 81 => eapply cp_eq_refl
  | 82 => match goal with
    | E : proof_certificate ?n ?g (Equal ?x ?y),
      R : renames (UnbindMap ?x) ?p ?px,
      S : renames (UnbindMap ?y) ?p ?py |- proof_certificate ?n ?g ?py =>
        eapply (cp_eq_subst n g p px py x y)
    end
  | _ => idtac
  end.
Ltac conclude_meaning :=
  lazymatch goal with
  | |- atomic_meaning tType ?t => apply am_type
  | |- atomic_meaning (tConst 0) ?t => let n := read_index t in exact (am_index n)
  | |- atomic_meaning (tConst 3) ?t => let p := read_formula t in exact (am_formula p)
  | |- atomic_meaning (tConst 18) ?t => let r := read_map t in exact (am_map r)
  | |- atomic_meaning (tConst 52) ?t => let g := read_context t in exact (am_context g)
  | |- atomic_meaning (tApp (tApp (tConst 9) ?x) ?y) ?t =>
    let i := read_index x in let n := read_index y in apply (am_lt i n t)
  | |- atomic_meaning (tApp (tApp (tConst 12) ?x) ?y) ?t =>
    let n := read_index x in let p := read_formula y in apply (am_scope n p t)
  | |- atomic_meaning (tApp (tApp (tApp (tConst 26) ?x) ?y) ?z) ?t =>
    let r := read_map x in let i := read_index y in let j := read_index z in apply (am_maps r i j t); choose_rule t
  | |- atomic_meaning (tApp (tApp (tApp (tConst 43) ?x) ?y) ?z) ?t =>
    let r := read_map x in let p := read_formula y in let q := read_formula z in apply (am_rename r p q t); choose_rule t
  | |- atomic_meaning (tApp (tApp (tApp (tConst 49) ?x) ?y) ?z) ?t =>
    let n := read_index x in let p := read_formula y in let q := read_formula z in apply (am_close n p q t); choose_rule t
  | |- atomic_meaning (tApp (tApp (tConst 55) ?x) ?y) ?t =>
    let p := read_formula x in let g := read_context y in apply (am_in p g t)
  | |- atomic_meaning (tApp (tApp (tConst 58) ?x) ?y) ?t =>
    let g := read_context x in let h := read_context y in apply (am_lifts g h t); choose_rule t
  | |- atomic_meaning (tApp (tConst 61) ?x) ?t =>
    let p := read_formula x in apply (am_axiom p t); choose_rule t
  | |- atomic_meaning (tApp (tApp (tApp (tConst 72) ?x) ?y) ?z) ?t =>
    let n := read_index x in let g := read_context y in let p := read_formula z in apply (am_proof n g p t); choose_rule t
  end.

Lemma constant_meaning k a : nth_error zfc_signature k = Some a -> realizes (pi_count a) a (tConst k).
Proof.
  intros K.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|rest]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  all: cbn [nth_error zfc_signature map prelude declared_type] in K.
  all: try (destruct rest; discriminate).
  all: inversion K; subst a; clear K.
  all: repeat first [progress reduce_reflection | let v := fresh "arg" in let G := fresh "Ground" in let A := fresh "Meaning" in
    intros v G A; invert_meaning].
  all: conclude_meaning.
  all: eauto 4.
  all: try lia.
  all: try (cbn [scoped]; apply andb_true_iff; split; apply Nat.ltb_lt; assumption).
  all: try (cbn [scoped]; apply andb_true_iff; auto).
  all: try (cbn [scoped]; assumption).
  all: try (cbn; auto).

Qed.

Theorem ground_meaning t a : ground_typing zfc_signature t a -> realizes (pi_count a) a t.
Proof.
  intros H; induction H.
  - eapply constant_meaning; exact H.
  - pose proof (ground_type_first_order _ _ H) as FO.
    inversion FO; subst; try match goal with F : flat (tPi _ _) |- _ => inversion F end.
    pose proof (ground_typing_ground _ _ _ H0) as GX.
    unfold instantiate at 1; rewrite pi_count_subst by assumption.
    cbn [pi_count realizes] in IHground_typing1.
    apply IHground_typing1; [exact GX|].
    apply (proj1 (flat_realizes (pi_count a) a x H3)); exact IHground_typing2.
Qed.

Lemma proof_type_flat p : flat (proof_type p).
Proof.
  assert (FI : forall n, flat (encode_index n)).
  { intros n; induction n; cbn [encode_index]; constructor; auto; constructor. }
  assert (FF : forall q, flat (encode q)).
  { intros q; induction q; cbn [encode]; repeat constructor; auto. }
  unfold proof_type; repeat constructor; auto.
Qed.

Theorem typed_proof_recovered p t : typing zfc_signature [] t (proof_type p) -> proof_certificate 0 [] p.
Proof.
  intros T.
  destruct (typing_evaluates _ _ _ _ zfc_signature_wf (wf_context_nil _) T) as [u E].
  pose proof (subject_reduction_parallel_steps _ _ _ _ _ zfc_signature_wf (evaluates_steps _ _ E) T) as U.
  pose proof (normal_atomic_ground zfc_signature zfc_signature_first_order u (proof_type p)
    (evaluates_normal_form _ _ E) U (proof_type_flat p)) as G.
  pose proof (ground_meaning _ _ G) as M.
  apply (proj1 (flat_realizes (pi_count (proof_type p)) (proof_type p) u (proof_type_flat p))) in M.
  unfold proof_type in M; invert_meaning; assumption.
Qed.

Theorem typed_ZFC_sound p t : typing zfc_signature [] t (proof_type p) -> ZFC_proves p.
Proof. intros T; apply proof_certificate_sound; eapply typed_proof_recovered; exact T. Qed.
Theorem concrete_declarative_presentation : declarative_presentation zfc_signature proof_type.
Proof.
  constructor.
  - apply zfc_signature_wf.
  - intros p Closed; apply proof_type_sorted.
  - intros p t Closed T; eapply typed_ZFC_sound; exact T.
  - apply ZFC_translation.
Qed.
Theorem concrete_correct_presentation : correct_presentation zfc_signature proof_type.
Proof. apply declarative_to_correct; exact concrete_declarative_presentation. Qed.
Theorem ZFC_pa_iff p : sentence p ->
  (ZFC_proves p <-> exists t fuel, check fuel zfc_signature t (proof_type p) = true).
Proof. apply presentation_iff; exact concrete_correct_presentation. Qed.

Print Assumptions normal_atomic_ground.
Print Assumptions constant_meaning.
Print Assumptions typed_proof_recovered.
Print Assumptions ZFC_pa_iff.

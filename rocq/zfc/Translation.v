From Stdlib Require Import List PeanoNat Bool Lia.
From Proofglyph.Language Require Import Syntax Kernel Program Substitution TypingSubstitution WellFormed CachedChecker.
From Proofglyph.Zfc Require Import Formula Axioms Deduction Encoding Certificates Specification.
From Proofglyph.ZfcDeep Require Import Artifact DeepVerification.
Import ListNotations.

Fixpoint encode_map r := match r with
| ShiftMap => tConst 19 | UnbindMap x => tApp (tConst 20) (encode_index x)
| UpMap r => tApp (tConst 21) (encode_map r)
| SepMap => tConst 22 | ValueMap => tConst 23 | UniqueMap => tConst 24 | ImageMap => tConst 25
end.
Fixpoint encode_context g := match g with
| [] => tConst 53 | p :: g => tApp (tApp (tConst 54) (encode p)) (encode_context g)
end.
Definition lt_type x n := tApp (tApp (tConst 9) (encode_index x)) (encode_index n).
Definition maps_type r i j := tApp (tApp (tApp (tConst 26) (encode_map r)) (encode_index i)) (encode_index j).
Definition in_type p g := tApp (tApp (tConst 55) (encode p)) (encode_context g).
Definition lifts_type g h := tApp (tApp (tConst 58) (encode_context g)) (encode_context h).
Definition derives_type n g p :=
  tApp (tApp (tApp (tConst 71) (encode_index n)) (encode_context g)) (encode p).

Lemma subst_index d v n : subst d v (encode_index n) = encode_index n.
Proof. induction n; cbn [encode_index subst]; congruence. Qed.
Lemma subst_formula d v p : subst d v (encode p) = encode p.
Proof. induction p; cbn [encode subst]; rewrite ?subst_index; congruence. Qed.
Lemma subst_map d v r : subst d v (encode_map r) = encode_map r.
Proof. induction r; cbn [encode_map subst]; rewrite ?subst_index; congruence. Qed.
Lemma subst_context d v g : subst d v (encode_context g) = encode_context g.
Proof. induction g; cbn [encode_context subst]; rewrite ?subst_formula; congruence. Qed.
Lemma shift_index_code d c n : shift d c (encode_index n) = encode_index n.
Proof. induction n; cbn [encode_index shift]; congruence. Qed.
Lemma shift_formula_code d c p : shift d c (encode p) = encode p.
Proof. induction p; cbn [encode shift]; rewrite ?shift_index_code; congruence. Qed.
Lemma shift_map_code d c r : shift d c (encode_map r) = encode_map r.
Proof. induction r; cbn [encode_map shift]; rewrite ?shift_index_code; congruence. Qed.
Lemma shift_context_code d c g : shift d c (encode_context g) = encode_context g.
Proof. induction g; cbn [encode_context shift]; rewrite ?shift_formula_code; congruence. Qed.
Create HintDb codes.
#[local] Hint Rewrite subst_index subst_formula subst_map subst_context
  shift_index_code shift_formula_code shift_map_code shift_context_code : codes.

Fixpoint apps f xs := match xs with [] => f | x :: xs => apps (tApp f x) xs end.
Inductive arguments_typed : term -> list term -> term -> Prop :=
| args_nil : forall a, arguments_typed a [] a
| args_cons : forall a b x xs c, typing zfc_signature [] x a ->
    arguments_typed (instantiate b x) xs c -> arguments_typed (tPi a b) (x :: xs) c.
Lemma arguments_sound a xs c : arguments_typed a xs c ->
  forall f, typing zfc_signature [] f a -> typing zfc_signature [] (apps f xs) c.
Proof. intros H; induction H; intros f F; cbn [apps]; [exact F|apply IHarguments_typed; eapply ty_app; eauto]. Qed.
Lemma constant_application k a xs c : nth_error zfc_signature k = Some a ->
  arguments_typed a xs c -> typing zfc_signature [] (apps (tConst k) xs) c.
Proof. intros K A; eapply arguments_sound; [exact A|apply ty_const; exact K]. Qed.

Ltac reduce_codes :=
  repeat (progress (cbn [instantiate subst shift Nat.eqb Nat.ltb Nat.leb Nat.pred Nat.add]; autorewrite with codes)).
Ltac use_constant k data :=
  let xs := open_constr:(List.app data (_ : list term)) in
  let entry := eval cbv [nth_error zfc_signature map prelude declared_type] in
    (nth_error zfc_signature k) in
  lazymatch entry with Some ?ty =>
    eexists (apps (tConst k) xs); eapply (constant_application k ty xs);
    [reflexivity|reduce_codes]
  end.

Lemma index_code_typed n : typing zfc_signature [] (encode_index n) index_type.
Proof. rewrite signature_prefix; apply typing_extend; apply index_typed. Qed.
Lemma map_code_typed r : typing zfc_signature [] (encode_map r) (tConst 18).
Proof.
  induction r; cbn [encode_map]; try (apply ty_const; reflexivity).
  - change (typing zfc_signature [] (tApp (tConst 20) (encode_index x))
      (instantiate (tConst 18) (encode_index x))).
    eapply ty_app; [apply ty_const; reflexivity|apply index_code_typed].
  - change (typing zfc_signature [] (tApp (tConst 21) (encode_map r))
      (instantiate (tConst 18) (encode_map r))).
    eapply ty_app; [apply ty_const; reflexivity|exact IHr].
Qed.
Lemma context_code_typed g : typing zfc_signature [] (encode_context g) (tConst 52).
Proof.
  induction g; cbn [encode_context]; [apply ty_const; reflexivity|].
  change (typing zfc_signature [] (tApp (tApp (tConst 54) (encode a)) (encode_context g))
    (instantiate (tConst 52) (encode_context g))).
  eapply ty_app; [|exact IHg].
  change (typing zfc_signature [] (tApp (tConst 54) (encode a))
    (instantiate (tPi (tConst 52) (tConst 52)) (encode a))).
  eapply ty_app; [apply ty_const; reflexivity|apply formula_code_typed].
Qed.

Ltac type_arguments :=
  reduce_codes;
  first [solve [apply args_nil]
  | multimatch goal with H : typing zfc_signature [] _ _ |- _ =>
      eapply args_cons; [exact H|type_arguments] end
  | solve [eapply args_cons; [eapply formula_code_typed|type_arguments]]
  | solve [eapply args_cons; [eapply index_code_typed|type_arguments]]
  | solve [eapply args_cons; [eapply map_code_typed|type_arguments]]
  | solve [eapply args_cons; [eapply context_code_typed|type_arguments]]].

(** Collect witnesses once; signature application infers each evidence argument
    from its required type rather than naming witnesses in every rule case. *)
Ltac unpack_translations :=
  repeat match goal with H : exists t, typing zfc_signature [] t _ |- _ =>
    destruct H as [? ?] end.
Ltac collect_translation lemma :=
  repeat match goal with H : _ |- _ =>
    let E := fresh "translated" in
    eassert (E : exists t, typing zfc_signature [] t _) by (eapply lemma; exact H);
    clear H; destruct E as [? ?]
  end.

(** Search only the contiguous signature block for the source judgment.
    Each candidate must finish the entire kernel-checked typing derivation. *)
Ltac translation_rules lo hi :=
  first [solve [use_constant lo (@nil term); type_arguments]
  | lazymatch eval compute in (lo <? hi) with
    | true => let next := eval compute in (S lo) in translation_rules next hi
    | false => fail "no applicable LF rule in signature block"
    end].

Lemma lt_translation x n : x < n -> exists t, typing zfc_signature [] t (lt_type x n).
Proof.
  revert x; induction n; intros x L; [lia|].
  destruct x as [|x].
  - use_constant 10 [encode_index n]; type_arguments.
  - destruct (IHn x ltac:(lia)) as [t T].
    use_constant 11 [encode_index x; encode_index n; t]; type_arguments.
Qed.

Lemma scope_translation p : forall n, scoped n p = true ->
  exists t, typing zfc_signature [] t (scoped_type (encode_index n) (encode p)).
Proof.
  induction p; intros n H; cbn [scoped] in H.
  - use_constant 13 [encode_index n]; type_arguments.
  - apply andb_true_iff in H as [X Y]; apply Nat.ltb_lt in X; apply Nat.ltb_lt in Y.
    destruct (lt_translation x n X) as [u U], (lt_translation y n Y) as [v V].
    use_constant 14 [encode_index n; encode_index x; encode_index y; u; v]; type_arguments.
  - apply andb_true_iff in H as [X Y]; apply Nat.ltb_lt in X; apply Nat.ltb_lt in Y.
    destruct (lt_translation x n X) as [u U], (lt_translation y n Y) as [v V].
    use_constant 15 [encode_index n; encode_index x; encode_index y; u; v]; type_arguments.
  - apply andb_true_iff in H as [P Q].
    destruct (IHp1 n P) as [u U], (IHp2 n Q) as [v V].
    use_constant 16 [encode_index n; encode p1; encode p2; u; v]; type_arguments.
  - destruct (IHp (S n) H) as [t T].
    use_constant 17 [encode_index n; encode p; t]; type_arguments.
Qed.

Lemma maps_translation r i j : maps r i j -> exists t, typing zfc_signature [] t (maps_type r i j).
Proof.
  intros H; induction H; unpack_translations;
    translation_rules 27 42.
Qed.

Lemma renames_translation r p q : renames r p q ->
  exists t, typing zfc_signature [] t (rename_type (encode_map r) (encode p) (encode q)).
Proof.
  intros H; induction H; unpack_translations; collect_translation maps_translation;
    translation_rules 44 48.
Qed.

Lemma closes_translation n p q : closes n p q ->
  exists t, typing zfc_signature [] t (close_type (encode_index n) (encode p) (encode q)).
Proof.
  intros H; induction H; unpack_translations;
    translation_rules 50 51.
Qed.
Lemma in_translation p g : In p g -> exists t, typing zfc_signature [] t (in_type p g).
Proof.
  induction g as [|q g IH]; intros H; [contradiction|].
  destruct H as [E|H].
  - subst q; translation_rules 56 56.
  - destruct (IH H) as [t T]. translation_rules 57 57.
Qed.
Lemma lifts_translation g h : lifts g h -> exists t, typing zfc_signature [] t (lifts_type g h).
Proof.
  intros H; induction H; unpack_translations; collect_translation renames_translation;
    translation_rules 59 60.
Qed.

Theorem axiom_translation p : axiom_certificate p ->
  exists t, typing zfc_signature [] t (zax (encode p)).
Proof.
  intros H; destruct H; unpack_translations;
    collect_translation scope_translation; collect_translation renames_translation;
    collect_translation closes_translation;
    translation_rules 62 70.
Qed.

Theorem certificate_translation n g p : proof_certificate n g p ->
  exists t, typing zfc_signature [] t (derives_type n g p).
Proof.
  intros H; induction H; unpack_translations;
    collect_translation scope_translation; collect_translation in_translation;
    collect_translation axiom_translation; collect_translation lifts_translation;
    collect_translation lt_translation; collect_translation renames_translation;
    translation_rules 72 81.
Qed.

Corollary ZFC_translation p : ZFC_proves p -> exists t, typing zfc_signature [] t (proof_type p).
Proof.
  intros H; apply proof_certificate_complete in H.
  exact (certificate_translation 0 [] p H).
Qed.
Theorem ZFC_accepted p : ZFC_proves p ->
  exists t bound, forall fuel, bound <= fuel -> check fuel zfc_signature t (proof_type p) = true.
Proof.
  apply typed_translation_accepted; [apply zfc_signature_wf| |apply ZFC_translation].
  intros q Closed; apply proof_type_sorted.
Qed.

Print Assumptions certificate_translation.
Print Assumptions ZFC_translation.
Print Assumptions ZFC_accepted.

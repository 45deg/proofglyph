From Stdlib Require Import List Permutation PeanoNat Lia.
From Rocq4pa Require Import Syntax Substitution Program WellFormed Evaluation
  Confluence Generation Preservation TypedNormalization Checker.
From Calculi Require Import Calculi Encoding Verification Derivations CutElimination.
Import ListNotations.

(** The fixed signature has first-order domains: none of its constants takes
    an LF function as an argument. Normal inhabitants therefore have algebraic
    spines, although the original proof may contain arbitrary beta redexes. *)
Inductive object_syntax : term -> Prop :=
| os_var : forall n, object_syntax (tVar n)
| os_const : forall n, object_syntax (tConst n)
| os_app : forall f x, object_syntax f -> object_syntax x -> object_syntax (tApp f x).
Inductive telescope : term -> Prop :=
| tel_object : forall t, object_syntax t -> telescope t
| tel_type : telescope tType
| tel_pi : forall a b, object_syntax a -> telescope b -> telescope (tPi a b).

Lemma object_normal t : object_syntax t -> normal_form t.
Proof.
  intros H; induction H; constructor; auto.
  intros a b E; subst; inversion H.
Qed.
Lemma object_not_pi t : object_syntax t -> forall a b, t <> tPi a b.
Proof. intros H; inversion H; discriminate. Qed.
Lemma telescope_normal t : telescope t -> normal_form t.
Proof. intros H; induction H; eauto using object_normal, normal_form. Qed.
Lemma object_shift t : object_syntax t -> forall n k, object_syntax (shift n k t).
Proof. intros H; induction H; intros; cbn [shift]; constructor; auto. Qed.
Lemma object_subst t : object_syntax t -> forall n x, object_syntax x -> object_syntax (subst n x t).
Proof.
  intros H; induction H; intros depth value X; cbn [subst].
  - destruct (n =? depth); [apply object_shift; exact X|constructor].
  - constructor.
  - constructor; auto.
Qed.
Lemma telescope_subst t : telescope t -> forall n x,
  object_syntax x -> telescope (subst n x t).
Proof.
  intros H; induction H; intros; cbn [subst];
    eauto using telescope, object_subst.
Qed.
Lemma telescope_pi_parts a b : telescope (tPi a b) -> object_syntax a /\ telescope b.
Proof. intros H; inversion H; subst; [inversion H0|auto]. Qed.

Lemma signature_telescopes : Forall telescope fixed_signature.
Proof.
  cbv [fixed_signature Artifact.prelude declared_type map].
  repeat first [apply tel_pi | apply tel_type | apply tel_object | constructor].
Qed.

Inductive algebraic : term -> term -> Prop :=
| alg_const : forall n a, nth_error fixed_signature n = Some a -> algebraic (tConst n) a
| alg_app : forall f x a b, algebraic f (tPi a b) -> algebraic x a ->
    algebraic (tApp f x) (instantiate b x).
Lemma algebraic_invariants t a : algebraic t a -> object_syntax t /\ telescope a.
Proof.
  intros H; induction H.
  - split; [constructor|]. apply (proj1 (Forall_forall _ _) signature_telescopes). eapply nth_error_In; exact H.
  - destruct IHalgebraic1 as [F T], IHalgebraic2 as [X A].
    apply telescope_pi_parts in T as [_ B]; split; [constructor; auto|].
    apply telescope_subst; assumption.
Qed.

Lemma normal_not_pi t : normal_form t -> (forall a b, t <> tPi a b) ->
  forall a b, ~ conv (tPi a b) t.
Proof.
  intros N NP a b C; destruct (conv_joins _ _ C) as [u [P T]].
  pose proof (steps_normal_form _ _ T N) as E; subst u.
  destruct (steps_pi_inv _ _ P _ _ eq_refl) as [a' [b' [E _]]].
  eapply NP; exact E.
Qed.
Lemma object_not_sort_conv t s : object_syntax t -> is_sort s -> ~ conv s t.
Proof.
  intros T [->| ->] C;
    assert (E : _ = t) by (eapply normal_forms_unique; eauto using normal_form, object_normal);
    subst; inversion T.
Qed.

(** The last two alternatives isolate abstractions and type/kind expressions;
    neither can inhabit a first-order domain of this signature. *)
Theorem normal_typed_classification t a : normal_form t -> typing fixed_signature [] t a ->
  (exists b, algebraic t b /\ conv b a) \/
  (exists x y, t = tLam x y) \/ (conv tType a \/ conv tKind a).
Proof.
  revert a; induction t; intros target N T;
    apply typing_generation in T; cbn [generates] in T.
  - right; right; auto.
  - contradiction.
  - destruct T as [a [E C]]; destruct n; discriminate.
  - destruct T as [a [E C]]; left; exists a; split; [constructor|]; assumption.
  - destruct T as [s [A [B [S C]]]]; right; right; destruct S as [->| ->]; auto.
  - right; left; eauto.
  - destruct T as [a [b [F [X C]]]].
    inversion N; subst.
    destruct (IHt1 _ H1 F) as [[ft [AF CF]]|[[x [y E]]|[S|S]]].
    + destruct (algebraic_invariants _ _ AF) as [OF TF].
      inversion TF; subst.
      * exfalso; eapply normal_not_pi; [apply object_normal; eassumption|apply object_not_pi; eassumption|apply cv_sym; exact CF].
      * exfalso; eapply normal_not_pi; [constructor|intros; discriminate|apply cv_sym; exact CF].
      * destruct (conv_pi_injective _ _ _ _ CF) as [AC BC].
        assert (XT : typing fixed_signature [] t2 a0) by (eapply ty_conv; [exact X|apply cv_sym; exact AC]).
        destruct (IHt2 _ H2 XT) as [[xt [AX CX]]|[[x [y E]]|[S|S]]].
        -- destruct (algebraic_invariants _ _ AX) as [_ TX].
           assert (EQ : xt = a0) by (eapply normal_forms_unique; eauto using telescope_normal, object_normal).
           subst xt; left; exists (instantiate b0 t2); split; [econstructor; eauto|].
           eapply cv_trans; [|exact C]. rewrite !instantiate_as_substitute.
           apply conv_substitute; exact BC.
        -- subst t2; apply typing_generation in XT; cbn [generates] in XT.
           destruct XT as [bt [s [D [Y [PI [SS BAD]]]]]].
           exfalso; eapply normal_not_pi; [apply object_normal; eassumption|apply object_not_pi; eassumption|exact BAD].
        -- exfalso; eapply object_not_sort_conv; [eassumption|left; reflexivity|exact S].
        -- exfalso; eapply object_not_sort_conv; [eassumption|right; reflexivity|exact S].
    + exfalso; eapply H3; exact E.
    + exfalso; eapply normal_not_pi; [constructor|intros; discriminate|apply cv_sym; exact S].
    + exfalso; eapply normal_not_pi; [constructor|intros; discriminate|apply cv_sym; exact S].
Qed.

Fixpoint pi_depth t := match t with tPi _ b => S (pi_depth b) | _ => 0 end.
Lemma object_pi_depth t : object_syntax t -> pi_depth t = 0.
Proof. intros H; inversion H; reflexivity. Qed.
Lemma telescope_subst_depth t : telescope t -> forall depth x, object_syntax x ->
  pi_depth (subst depth x t) = pi_depth t.
Proof.
  intros H; induction H; intros; cbn [subst pi_depth]; auto.
  - rewrite (object_pi_depth _ (object_subst _ H _ _ H0)), (object_pi_depth _ H); reflexivity.
Qed.

(** Ground realizability records the intended source judgment. It does not
    inspect the proof term; data arguments must be canonical encodings. *)
Definition ground_meaning a t : Prop := match a with
| tConst 0 => exists i, t = encode_index i
| tConst 3 => exists f, t = encode f
| tConst 11 => exists g, t = encode_context g
| tApp (tApp (tConst 14) a) g => match decode a, decode_context g with
    | Some a, Some g => In a g | _, _ => False end
| tApp (tApp (tConst 17) g) h => match decode_context g, decode_context h with
    | Some g, Some h => Permutation g h | _, _ => False end
| tApp (tApp (tConst 22) g) a => match decode_context g, decode a with
    | Some g, Some a => NK g a | _, _ => False end
| tApp (tApp (tConst 37) g) d => match decode_context g, decode_context d with
    | Some g, Some d => LK g d | _, _ => False end
| tType => True
| _ => False
end.
Fixpoint meaning fuel a t : Prop := match a with
| tPi dom cod => match fuel with
    | 0 => False
    | S fuel => forall x, ground_meaning dom x ->
        meaning fuel (instantiate cod x) (tApp t x)
    end
| _ => ground_meaning a t
end.
Lemma meaning_object fuel a t : object_syntax a -> meaning fuel a t = ground_meaning a t.
Proof. intros H; destruct fuel; inversion H; reflexivity. Qed.

Ltac simplify_meaning :=
  cbn [instantiate subst shift Nat.eqb Nat.ltb Nat.leb Nat.add Nat.pred];
  repeat rewrite shift_formula_code;
  repeat rewrite shift_context_code;
  repeat rewrite shift_index_code;
  repeat rewrite subst_formula_code;
  repeat rewrite subst_context_code;
  repeat rewrite subst_index_code;
  cbn [ground_meaning decode decode_binary decode_context] in *;
  repeat rewrite formula_roundtrip in *;
  repeat rewrite context_roundtrip in *;
  repeat rewrite index_roundtrip in *;
  cbn [decode_binary] in *.

Ltac meaning_arguments :=
  match goal with
  | |- meaning ?fuel (tPi ?dom ?cod) ?t =>
    destruct fuel as [|fuel]; [cbn [pi_depth] in *; lia|];
    cbn [meaning]; let x := fresh "argument" in let X := fresh "realizes" in
    intros x X; cbn [ground_meaning] in X;
    try (destruct X as [? E]; subst x);
    simplify_meaning; meaning_arguments
  | |- meaning ?fuel _ _ => destruct fuel; cbn [meaning]; simplify_meaning
  end.

Ltac meaning_data :=
  match goal with
  | |- exists i, tConst 1 = encode_index i => exists 0
  | |- exists i, tApp (tConst 2) (encode_index ?j) = encode_index i => exists (S j)
  | |- exists f, tApp (tConst 4) (encode_index ?i) = encode f => exists (Atom i)
  | |- exists f, tConst 5 = encode f => exists Bottom
  | |- exists f, tConst 6 = encode f => exists Top
  | |- exists f, tApp (tApp (tConst 7) (encode ?a)) (encode ?b) = encode f => exists (Imp a b)
  | |- exists f, tApp (tApp (tConst 8) (encode ?a)) (encode ?b) = encode f => exists (Conj a b)
  | |- exists f, tApp (tApp (tConst 9) (encode ?a)) (encode ?b) = encode f => exists (Disj a b)
  | |- exists f, tApp (tConst 10) (encode ?a) = encode f => exists (Neg a)
  | |- exists g, tConst 12 = encode_context g => exists []
  | |- exists g, tApp (tApp (tConst 13) (encode ?a)) (encode_context ?h) = encode_context g => exists (a :: h)
  end; reflexivity.

Lemma constant_meaning n a : nth_error fixed_signature n = Some a ->
  forall fuel, pi_depth a <= fuel -> meaning fuel a (tConst n).
Proof.
  intros E fuel B.
  do 56 (destruct n as [|n]; [
    cbn [fixed_signature Artifact.prelude declared_type map nth_error] in E;
    inversion E; subst a; clear E;
    meaning_arguments; try meaning_data;
    simpl in *; try reflexivity; eauto 3 using nk_assume, nk_top, nk_bottom, nk_imp_intro, nk_imp_elim, nk_conj_intro, nk_conj_left, nk_conj_right, nk_disj_left, nk_disj_right, nk_disj_elim, nk_neg_intro, nk_neg_elim, nk_classical, lk_identity, lk_bottom, lk_top, lk_weak_left, lk_weak_right, lk_contract_left, lk_contract_right, lk_exchange_left, lk_exchange_right, lk_imp_right, lk_imp_left, lk_conj_left, lk_conj_right, lk_disj_left, lk_disj_right, lk_neg_left, lk_neg_right, lk_cut, perm_nil, perm_skip, perm_swap, Permutation_trans; tauto
    |]).
  cbn [fixed_signature Artifact.prelude declared_type map nth_error] in E.
  destruct n; discriminate.
Qed.

Theorem algebraic_meaning t a : algebraic t a -> forall fuel,
  pi_depth a <= fuel -> meaning fuel a t.
Proof.
  intros H; induction H; intros fuel B.
  - apply constant_meaning; assumption.
  - destruct (algebraic_invariants _ _ H) as [_ TF].
    destruct (algebraic_invariants _ _ H0) as [OX _].
    apply telescope_pi_parts in TF as [OA TB].
    assert (D : pi_depth (instantiate b x) = pi_depth b)
      by (apply telescope_subst_depth; assumption).
    assert (F : meaning (S fuel) (tPi a b) f)
      by (apply IHalgebraic1; cbn [pi_depth]; lia).
    cbn [meaning] in F; apply F.
    pose proof (IHalgebraic2 0) as X.
    rewrite meaning_object in X by exact OA; apply X.
    rewrite object_pi_depth by exact OA; lia.
Qed.

Lemma object_inhabitant_algebraic t a : object_syntax a -> normal_form t ->
  typing fixed_signature [] t a -> algebraic t a.
Proof.
  intros A N T.
  destruct (normal_typed_classification _ _ N T) as [[b [B C]]|[[x [y E]]|[S|S]]].
  - destruct (algebraic_invariants _ _ B) as [_ BT].
    assert (E : b = a) by (eapply normal_forms_unique; eauto using telescope_normal, object_normal).
    subst b; exact B.
  - subst t; apply typing_generation in T; cbn [generates] in T.
    destruct T as [bt [s [D [Y [PI [SS BAD]]]]]].
    exfalso; eapply normal_not_pi; [apply object_normal; exact A|apply object_not_pi; exact A|exact BAD].
  - exfalso; eapply object_not_sort_conv; [exact A|left; reflexivity|exact S].
  - exfalso; eapply object_not_sort_conv; [exact A|right; reflexivity|exact S].
Qed.
Theorem closed_object_restoration t a : object_syntax a -> lf a t ->
  exists u, evaluates t u /\ algebraic u a.
Proof.
  intros A T; destruct (typing_evaluates _ _ _ _ prelude_well_formed
    (wf_context_nil _) T) as [u E].
  exists u; split; [exact E|].
  apply object_inhabitant_algebraic; [exact A|eapply evaluates_normal_form; exact E|].
  eapply subject_reduction_parallel_steps; [exact prelude_well_formed|apply evaluates_steps; exact E|exact T].
Qed.

Lemma index_object i : object_syntax (encode_index i).
Proof. induction i; cbn [encode_index]; constructor; auto using object_syntax. Qed.
Lemma formula_object a : object_syntax (encode a).
Proof.
  induction a; cbn [encode]; unfold code_binary;
    repeat constructor; auto using index_object.
Qed.
Lemma context_object g : object_syntax (encode_context g).
Proof.
  induction g; cbn [encode_context]; unfold code_binary;
    repeat constructor; auto using formula_object.
Qed.
Lemma NK_code_object g a : object_syntax (NK_code g a).
Proof. unfold NK_code, nk_type; repeat constructor; auto using formula_object, context_object. Qed.
Lemma LK_code_object g d : object_syntax (LK_code g d).
Proof. unfold LK_code, lk_type; repeat constructor; auto using context_object. Qed.

Theorem LF_restores_NK g a t : lf (NK_code g a) t -> NK g a.
Proof.
  intros T; destruct (closed_object_restoration _ _ (NK_code_object g a) T) as [u [E A]].
  pose proof (algebraic_meaning _ _ A 0) as M.
  rewrite object_pi_depth in M by apply NK_code_object.
  specialize (M (Nat.le_refl 0)).
  rewrite meaning_object in M by apply NK_code_object.
  unfold ground_meaning, NK_code, nk_type in M.
  rewrite context_roundtrip, formula_roundtrip in M; exact M.
Qed.
Theorem LF_restores_LK g d t : lf (LK_code g d) t -> LK g d.
Proof.
  intros T; destruct (closed_object_restoration _ _ (LK_code_object g d) T) as [u [E A]].
  pose proof (algebraic_meaning _ _ A 0) as M.
  rewrite object_pi_depth in M by apply LK_code_object.
  specialize (M (Nat.le_refl 0)).
  rewrite meaning_object in M by apply LK_code_object.
  unfold ground_meaning, LK_code, lk_type in M.
  rewrite !context_roundtrip in M; exact M.
Qed.
Corollary NK_LF_adequacy g a : NK g a <-> exists t, lf (NK_code g a) t.
Proof.
  split; [apply NK_has_lf_derivation|intros [t T]; eapply LF_restores_NK; exact T].
Qed.
Corollary LK_LF_adequacy g d : LK g d <-> exists t, lf (LK_code g d) t.
Proof.
  split; [apply LK_has_lf_derivation|intros [t T]; eapply LF_restores_LK; exact T].
Qed.

Corollary LF_restores_cut_free_LK g d t : lf (LK_code g d) t -> LK_cut_free g d.
Proof. intros T; apply LK_cut_elimination; eapply LF_restores_LK; exact T. Qed.

(** Acceptance is existential in fuel; a fixed bound need not suffice for
    arbitrarily large proofs. Byte parsing/writing is outside this theorem. *)
Corollary NK_checker_adequacy g a : NK g a <->
  exists t fuel, check fuel fixed_signature t (NK_code g a) = true.
Proof.
  split.
  - intros H; destruct (NK_has_lf_derivation _ _ H) as [t T].
    assert (S : sorted_type fixed_signature [] (NK_code g a)).
    { exists tType; split; [apply NK_code_is_type|left; reflexivity]. }
    destruct (declarative_check_complete _ _ _ prelude_well_formed S T) as [fuel F].
    exists t, fuel; apply F; reflexivity.
  - intros [t [fuel H]].
    destruct (check_sound _ _ _ _ prelude_well_formed H) as [T _].
    eapply LF_restores_NK; exact T.
Qed.
Corollary LK_checker_adequacy g d : LK g d <->
  exists t fuel, check fuel fixed_signature t (LK_code g d) = true.
Proof.
  split.
  - intros H; destruct (LK_has_lf_derivation _ _ H) as [t T].
    assert (S : sorted_type fixed_signature [] (LK_code g d)).
    { exists tType; split; [apply LK_code_is_type|left; reflexivity]. }
    destruct (declarative_check_complete _ _ _ prelude_well_formed S T) as [fuel F].
    exists t, fuel; apply F; reflexivity.
  - intros [t [fuel H]].
    destruct (check_sound _ _ _ _ prelude_well_formed H) as [T _].
    eapply LF_restores_LK; exact T.
Qed.

Print Assumptions LF_restores_NK.
Print Assumptions LF_restores_LK.
Print Assumptions NK_LF_adequacy.
Print Assumptions LK_LF_adequacy.
Print Assumptions LF_restores_cut_free_LK.
Print Assumptions NK_checker_adequacy.
Print Assumptions LK_checker_adequacy.

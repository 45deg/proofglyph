From Stdlib Require Import List PeanoNat Bool Lia.
From Proofglyph.Language Require Import Syntax Substitution Kernel WellFormed TypingSubstitution
  Evaluation Confluence Generation Preservation TypedNormalization.
Import ListNotations.

(** First-order LF signatures have no constructor taking a function argument.
    Normal closed object terms can consequently be read as constructor trees. *)
Inductive flat : term -> Prop :=
| flat_var : forall i, flat (tVar i)
| flat_const : forall k, flat (tConst k)
| flat_app : forall f x, flat f -> flat x -> flat (tApp f x).
Inductive ground : term -> Prop :=
| ground_const : forall k, ground (tConst k)
| ground_app : forall f x, ground f -> ground x -> ground (tApp f x).
Inductive first_order_type : term -> Prop :=
| fo_atom : forall a, flat a -> first_order_type a
| fo_type : first_order_type tType
| fo_pi : forall a b, flat a -> first_order_type b -> first_order_type (tPi a b).

Lemma ground_flat t : ground t -> flat t.
Proof. intros H; induction H; constructor; auto. Qed.
Lemma flat_normal t : flat t -> normal_form t.
Proof. intros H; induction H; constructor; auto; intros a b E; subst; inversion H. Qed.
Lemma first_order_normal t : first_order_type t -> normal_form t.
Proof. intros H; induction H; eauto using normal_form, flat_normal. Qed.
Lemma ground_shift t : ground t -> forall d c, shift d c t = t.
Proof. intros H; induction H; intros d c; cbn [shift]; congruence. Qed.
Lemma flat_subst t : flat t -> forall d v, ground v -> flat (subst d v t).
Proof.
  intros H; induction H; intros d v V; cbn [subst].
  - destruct (i =? d); [rewrite ground_shift by exact V; apply ground_flat; exact V|constructor].
  - constructor.
  - constructor; auto.
Qed.
Lemma first_order_subst t : first_order_type t -> forall d v, ground v -> first_order_type (subst d v t).
Proof.
  intros H; induction H; intros d v V; cbn [subst].
  - apply fo_atom; eapply flat_subst; eauto.
  - apply fo_type.
  - apply fo_pi; eauto using flat_subst.
Qed.

Lemma conv_pi_not_flat a b t : flat t -> ~ conv (tPi a b) t.
Proof.
  intros F C; destruct (conv_joins _ _ C) as [u [P T]].
  pose proof (steps_normal_form _ _ T (flat_normal _ F)) as E; subst u.
  destruct (steps_pi_inv _ _ P _ _ eq_refl) as [x [y [E _]]]; subst t; inversion F.
Qed.
Lemma conv_sort_not_pi s a b : is_sort s -> ~ conv s (tPi a b).
Proof.
  intros S C; destruct (conv_joins _ _ C) as [u [T P]].
  assert (N : normal_form s) by (destruct S as [->| ->]; constructor).
  pose proof (steps_normal_form _ _ T N) as E; subst u.
  destruct (steps_pi_inv _ _ P _ _ eq_refl) as [x [y [E _]]].
  destruct S as [->| ->]; discriminate.
Qed.
Definition neutral_head t := match t with tConst _ | tApp _ _ => true | _ => false end.
Lemma normal_function_neutral sg f x a b : normal_form (tApp f x) ->
  typing sg [] f (tPi a b) -> neutral_head f = true.
Proof.
  intros N T; inversion N; subst.
  destruct f; try reflexivity; apply typing_generation in T; cbn [generates] in T.
  - exfalso; eapply conv_sort_not_pi; [right; reflexivity|exact T].
  - contradiction.
  - destruct T as [u [E _]]; destruct n; discriminate.
  - destruct T as [s [_ [_ [S C]]]]; exfalso; eapply conv_sort_not_pi; eauto.
  - exfalso; eapply H3; reflexivity.
Qed.

Inductive ground_typing (sg : list term) : term -> term -> Prop :=
| gt_const : forall k a, nth_error sg k = Some a -> ground_typing sg (tConst k) a
| gt_app : forall f x a b, ground_typing sg f (tPi a b) -> ground_typing sg x a ->
    ground_typing sg (tApp f x) (instantiate b x).
Lemma ground_typing_ground sg t a : ground_typing sg t a -> ground t.
Proof. intros H; induction H; constructor; auto. Qed.
Lemma ground_typing_sound sg t a : ground_typing sg t a -> typing sg [] t a.
Proof. intros H; induction H; eauto using typing. Qed.

Section Canonical.
Variable sg : list term.
Hypothesis signature_first_order : forall k a, nth_error sg k = Some a -> first_order_type a.

Theorem normal_first_order t : forall a, normal_form t -> typing sg [] t a ->
  (neutral_head t = true \/ flat a) ->
  exists b, ground_typing sg t b /\ first_order_type b /\ conv b a.
Proof.
  induction t as [| |i|k|dom IHdom body IHbody|dom IHdom body IHbody|f IHf x IHx];
    intros a N T Shape.
  - destruct Shape as [E|F]; [discriminate|].
    apply typing_generation in T; cbn [generates] in T.
    pose proof (normal_forms_unique _ _ T nf_kind (flat_normal _ F)) as E; subst a; inversion F.
  - apply typing_generation in T; contradiction.
  - apply typing_generation in T; cbn [generates] in T; destruct T as [u [E _]]; destruct i; discriminate.
  - apply typing_generation in T; cbn [generates] in T; destruct T as [b [K C]].
    exists b; split; [constructor; exact K|split; [eapply signature_first_order; exact K|exact C]].
  - destruct Shape as [E|F]; [discriminate|].
    apply typing_generation in T; cbn [generates] in T; destruct T as [s [_ [_ [S C]]]].
    assert (NS : normal_form s) by (destruct S as [->| ->]; constructor).
    pose proof (normal_forms_unique _ _ C NS (flat_normal _ F)) as E; subst a.
    destruct S as [->| ->]; inversion F.
  - destruct Shape as [E|F]; [discriminate|].
    apply typing_generation in T; cbn [generates] in T; destruct T as [bt [s [_ [_ [_ [_ C]]]]]].
    exfalso; eapply conv_pi_not_flat; eauto.
  - inversion N as [| | | | | |f0 x0 NF NX NL]; subst.
    apply typing_generation in T; cbn [generates] in T.
    destruct T as [dom [body [FT [XT C]]]].
    destruct (IHf _ NF FT (or_introl (normal_function_neutral _ _ _ _ _ N FT))) as [b [GF [FO CF]]].
    inversion FO as [atom F| |dom' body' FD FB]; subst.
    + exfalso; eapply conv_pi_not_flat; [exact F|apply cv_sym; exact CF].
    + exfalso; eapply conv_sort_not_pi; [left; reflexivity|exact CF].
    + destruct (conv_pi_injective _ _ _ _ CF) as [CD CB].
      assert (XD : typing sg [] x dom') by (eapply ty_conv; [exact XT|apply cv_sym; exact CD]).
      destruct (IHx _ NX XD (or_intror FD)) as [actual [GX [FOX CX]]].
      assert (E : actual = dom') by (eapply normal_forms_unique; eauto using first_order_normal, flat_normal).
      subst actual; exists (instantiate body' x); split; [econstructor; eauto|split].
      * apply first_order_subst; [exact FB|eapply ground_typing_ground; exact GX].
      * eapply cv_trans; [|exact C]. rewrite !instantiate_as_substitute; apply conv_substitute; exact CB.
Qed.

Corollary normal_atomic_ground t a : normal_form t -> typing sg [] t a -> flat a -> ground_typing sg t a.
Proof.
  intros N T F; destruct (normal_first_order _ _ N T (or_intror F)) as [b [G [FO C]]].
  assert (E : b = a) by (eapply normal_forms_unique; eauto using first_order_normal, flat_normal).
  subst b; exact G.
Qed.
End Canonical.

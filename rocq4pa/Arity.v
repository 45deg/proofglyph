From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Substitution WellFormed TypingSubstitution
  Kernel Completeness Confluence Generation Preservation Regularity.
Import ListNotations.

Inductive arity : Type := base | arrow (a b : arity).

(** Object arguments cannot select a type constructor in lambda-Pi. Family
    abstractions/applications therefore contribute the shape of their body/head. *)
Fixpoint type_shape t : arity :=
  match t with
  | tPi a b => arrow (type_shape a) (type_shape b)
  | tLam _ b => type_shape b
  | tApp f _ => type_shape f
  | _ => base
  end.

Definition type_level sg ctx t :=
  typing sg ctx t tKind \/ exists k, typing sg ctx t k /\ typing sg ctx k tKind.

Lemma sort_type_level sg ctx s : is_sort s ->
  forall t, typing sg ctx t s -> type_level sg ctx t.
Proof. intros [->| ->] t T; [right; exists tType; split; [exact T|constructor]|left; exact T]. Qed.

Lemma type_level_typed sg ctx t : type_level sg ctx t -> exists k, typing sg ctx t k.
Proof. intros [T|[k [T K]]]; eauto. Qed.

Lemma type_level_pi sg ctx a b : type_level sg ctx (tPi a b) ->
  typing sg ctx a tType /\ type_level sg (a :: ctx) b.
Proof.
  intros L; destruct (type_level_typed _ _ _ L) as [k T].
  apply typing_generation in T; cbn [generates] in T.
  destruct T as [s [A [B [S C]]]]; split; [exact A|eapply sort_type_level; eauto].
Qed.

Lemma type_level_lam sg ctx a b : wf_signature sg -> wf_context sg ctx ->
  type_level sg ctx (tLam a b) ->
  typing sg ctx a tType /\ type_level sg (a :: ctx) b.
Proof.
  intros W CT [T|[k [T K]]].
  - pose proof (typing_kind_shape _ _ _ W CT T) as S; inversion S.
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [bt [s [A [B [PI [S C]]]]]].
    assert (SK : s = tKind).
    { eapply conv_sort_unique; [exact S|right; reflexivity|].
      eapply convertible_typing_unique; eauto. }
    subst s. apply typing_generation in PI; cbn [generates] in PI.
    destruct PI as [s [A' [BT [SS C']]]].
    assert (SK : s = tKind) by (eapply conv_sort_unique; [exact SS|right; reflexivity|exact C']).
    subst s; split; [exact A|right; exists bt; auto].
Qed.

Lemma type_level_app sg ctx f x : wf_signature sg -> wf_context sg ctx ->
  type_level sg ctx (tApp f x) -> type_level sg ctx f.
Proof.
  intros W CT [T|[k [T K]]].
  - pose proof (typing_kind_shape _ _ _ W CT T) as S; inversion S.
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [a [b [F [X C]]]].
    destruct (typing_function_regular _ _ _ _ _ W CT F) as [d [e [s [D [E [S [AD BE]]]]]]].
    assert (XD : typing sg ctx x d) by (eapply ty_conv; eauto).
    assert (RESULT : typing sg ctx (instantiate e x) s).
    { rewrite <- (instantiate_sort s x S). eapply typing_instantiate; eauto. }
    assert (EC : conv (instantiate e x) k).
    { eapply cv_trans; [|exact C]. rewrite !instantiate_as_substitute.
      apply conv_substitute; apply cv_sym; exact BE. }
    assert (SK : s = tKind).
    { eapply conv_sort_unique; [exact S|right; reflexivity|].
      eapply convertible_typing_unique; [exact W|exact RESULT|exact K|exact EC]. }
    subst s; right; exists (tPi d e); split.
    + eapply ty_conv; [exact F|apply cv_pi; assumption].
    + eapply ty_pi; [exact D|exact E|right; reflexivity].
Qed.

Lemma variable_not_type_level sg ctx n : wf_signature sg -> wf_context sg ctx ->
  ~ type_level sg ctx (tVar n).
Proof.
  intros W CT [T|[k [T K]]].
  - pose proof (typing_kind_shape _ _ _ W CT T) as S; inversion S.
  - apply typing_generation in T; cbn [generates] in T; destruct T as [a [LOOK C]].
    pose proof (wf_context_lookup _ _ _ _ W CT LOOK) as A.
    assert (BAD : tType = tKind).
    { eapply conv_sort_unique; [left; reflexivity|right; reflexivity|].
      eapply convertible_typing_unique; [exact W|exact A|exact K|exact C]. }
    discriminate.
Qed.

Theorem type_shape_substitution sg ctx t : wf_signature sg -> wf_context sg ctx ->
  type_level sg ctx t -> forall sub, type_shape (substitute sub t) = type_shape t.
Proof.
  intros W; revert ctx; induction t; intros ctx CT L sub; cbn [substitute type_shape]; try reflexivity.
  - exfalso; eapply variable_not_type_level; eauto.
  - destruct (type_level_pi _ _ _ _ L) as [A B]. f_equal.
    + eapply IHt1; [exact CT|right; exists tType; split; [exact A|constructor]].
    + eapply IHt2; [constructor; eauto|exact B].
  - destruct (type_level_lam _ _ _ _ W CT L) as [A B].
    eapply IHt2; [constructor; eauto|exact B].
  - eapply IHt1; [exact CT|eapply type_level_app; eauto].
Qed.

Lemma type_shape_rename r t : type_shape (rename r t) = type_shape t.
Proof. revert r; induction t; intros r; cbn [rename type_shape]; congruence. Qed.

Lemma type_level_reduction sg ctx t u : wf_signature sg -> reduces t u ->
  type_level sg ctx t -> type_level sg ctx u.
Proof.
  intros W R [T|[k [T K]]]; [left|right; exists k; split; [|exact K]];
    eapply subject_reduction; eauto.
Qed.

Theorem type_shape_reduction sg ctx t u : wf_signature sg -> wf_context sg ctx ->
  reduces t u -> type_level sg ctx t -> type_shape t = type_shape u.
Proof.
  intros W CT R; revert ctx CT; induction R; intros ctx CT L; cbn [type_shape].
  - pose proof (type_level_app _ _ _ _ W CT L) as F.
    destruct (type_level_lam _ _ _ _ W CT F) as [A B].
    rewrite instantiate_as_substitute; symmetry; eapply type_shape_substitution; [exact W|constructor; eauto|exact B].
  - destruct (type_level_pi _ _ _ _ L) as [A B]; f_equal.
    eapply IHR; [exact CT|right; exists tType; split; [exact A|constructor]].
  - destruct (type_level_pi _ _ _ _ L) as [A B]; f_equal.
    eapply IHR; [constructor; eauto|exact B].
  - reflexivity.
  - destruct (type_level_lam _ _ _ _ W CT L) as [A B].
    eapply IHR; [constructor; eauto|exact B].
  - eapply IHR; [exact CT|eapply type_level_app; eauto].
  - reflexivity.
Qed.

Lemma type_shape_steps sg ctx t u : wf_signature sg -> wf_context sg ctx ->
  beta_steps t u -> type_level sg ctx t -> type_shape t = type_shape u.
Proof.
  intros W CT R; induction R; intros L; [reflexivity|].
  transitivity (type_shape u).
  - eapply type_shape_reduction; eauto.
  - apply IHR; eapply type_level_reduction; eauto.
Qed.

Theorem type_shape_conversion sg ctx a b : wf_signature sg -> wf_context sg ctx ->
  type_level sg ctx a -> type_level sg ctx b -> conv a b -> type_shape a = type_shape b.
Proof.
  intros W CT A B C; destruct (conv_joins _ _ C) as [u [AU BU]].
  assert (TOB : forall t v, steps t v -> beta_steps t v).
  { intros t v R; induction R; eauto using beta_refl, beta_trans, parallel_beta_steps. }
  transitivity (type_shape u); [|symmetry]; eapply type_shape_steps; eauto.
Qed.

Definition proper_type sg ctx a := a = tKind \/ sorted_type sg ctx a.

Lemma sort_proper sg ctx s : is_sort s -> proper_type sg ctx s.
Proof.
  intros [->| ->]; [right; exists tKind; split; [constructor|right; reflexivity]|left; reflexivity].
Qed.

Lemma sorted_type_level sg ctx a : sorted_type sg ctx a -> type_level sg ctx a.
Proof. intros [s [T S]]; eapply sort_type_level; eauto. Qed.

Lemma proper_conv_shape sg ctx a b : wf_signature sg -> wf_context sg ctx ->
  proper_type sg ctx a -> proper_type sg ctx b -> conv a b -> type_shape a = type_shape b.
Proof.
  intros W CT [->|A] [->|B] C; try reflexivity.
  - exfalso; eapply sorted_not_conv_kind; [exact W|exact B|apply cv_sym; exact C].
  - exfalso; eapply sorted_not_conv_kind; [exact W|exact A|exact C].
  - eapply type_shape_conversion; eauto using sorted_type_level.
Qed.

Inductive arity_typing (sg : list arity) : list arity -> term -> arity -> Prop :=
| at_type : forall ctx, arity_typing sg ctx tType base
| at_var : forall ctx n a, nth_error ctx n = Some a -> arity_typing sg ctx (tVar n) a
| at_const : forall ctx n a, nth_error sg n = Some a -> arity_typing sg ctx (tConst n) a
| at_pi : forall ctx a b, arity_typing sg ctx a base ->
    arity_typing sg (type_shape a :: ctx) b base -> arity_typing sg ctx (tPi a b) base
| at_lam : forall ctx a b tau, arity_typing sg ctx a base ->
    arity_typing sg (type_shape a :: ctx) b tau ->
    arity_typing sg ctx (tLam a b) (arrow (type_shape a) tau)
| at_app : forall ctx f x sigma tau, arity_typing sg ctx f (arrow sigma tau) ->
    arity_typing sg ctx x sigma -> arity_typing sg ctx (tApp f x) tau.

Lemma type_shape_sort s : is_sort s -> type_shape s = base.
Proof. intros [->| ->]; reflexivity. Qed.

Theorem typing_arity sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx t a -> proper_type sg ctx a ->
  arity_typing (map type_shape sg) (map type_shape ctx) t (type_shape a).
Proof.
  intros W; revert ctx a; induction t; intros ctx typ CT T P;
    apply typing_generation in T; cbn [generates] in T.
  - assert (E : type_shape tKind = type_shape typ).
    { eapply proper_conv_shape; [exact W|exact CT|left; reflexivity|exact P|exact T]. }
    rewrite <- E; constructor.
  - contradiction.
  - destruct T as [a [LOOK C]].
    assert (E : type_shape (shift (S n) 0 a) = type_shape typ).
    { eapply proper_conv_shape; [exact W|exact CT| |exact P|exact C].
      right; exists tType; split; [eapply wf_context_lookup; eauto|left; reflexivity]. }
    rewrite <- E, shift_as_rename, type_shape_rename.
    constructor; rewrite nth_error_map, LOOK; reflexivity.
  - destruct T as [a [LOOK C]].
    assert (E : type_shape a = type_shape typ).
    { eapply proper_conv_shape; [exact W|exact CT| |exact P|exact C].
      right; apply sorted_type_any_context; [exact W|eapply wf_signature_lookup; eauto]. }
    rewrite <- E; constructor; rewrite nth_error_map, LOOK; reflexivity.
  - destruct T as [s [A [B [S C]]]].
    assert (E : type_shape s = type_shape typ).
    { eapply proper_conv_shape; eauto using sort_proper. }
    rewrite <- E, (type_shape_sort _ S); constructor.
    + apply IHt1 with (a := tType); [exact CT|exact A|apply sort_proper; left; reflexivity].
    + rewrite <- (type_shape_sort _ S). apply IHt2 with (ctx := t1 :: ctx) (a := s).
      * constructor; eauto.
      * exact B.
      * apply sort_proper; exact S.
  - destruct T as [bt [s [A [B [PI [S C]]]]]].
    assert (E : type_shape (tPi t1 bt) = type_shape typ).
    { eapply proper_conv_shape; [exact W|exact CT|right; exists s; auto|exact P|exact C]. }
    rewrite <- E; cbn [type_shape]; constructor.
    + apply IHt1 with (a := tType); [exact CT|exact A|apply sort_proper; left; reflexivity].
    + apply IHt2 with (ctx := t1 :: ctx) (a := bt); [constructor; eauto|exact B|].
      apply typing_generation in PI; cbn [generates] in PI.
      destruct PI as [k [_ [BT [K _]]]]; right; exists k; auto.
  - destruct T as [a [b [F [X C]]]].
    destruct (typing_function_regular _ _ _ _ _ W CT F) as [d [e [s [D [E [S [AD BE]]]]]]].
    assert (XD : typing sg ctx t2 d) by (eapply ty_conv; eauto).
    assert (FT : typing sg ctx t1 (tPi d e)).
    { eapply ty_conv; [exact F|apply cv_pi; assumption]. }
    assert (OUT : typing sg ctx (instantiate e t2) s).
    { rewrite <- (instantiate_sort s t2 S); eapply typing_instantiate; eauto. }
    assert (OC : conv (instantiate e t2) typ).
    { eapply cv_trans; [|exact C]. rewrite !instantiate_as_substitute.
      apply conv_substitute; apply cv_sym; exact BE. }
    assert (SH : type_shape (instantiate e t2) = type_shape typ).
    { eapply proper_conv_shape; [exact W|exact CT|right; exists s; auto|exact P|exact OC]. }
    rewrite instantiate_as_substitute in SH.
    rewrite (type_shape_substitution sg (d :: ctx) e W ltac:(constructor; eauto)
      (sort_type_level sg (d :: ctx) s S e E)) in SH.
    rewrite <- SH; eapply at_app with (sigma := type_shape d).
    + apply IHt1 with (a := tPi d e); [exact CT|exact FT|].
      right; exists s; split; [eapply ty_pi; eauto|exact S].
    + apply IHt2 with (a := d); [exact CT|exact XD|right; exists tType; split; [exact D|left; reflexivity]].
Qed.

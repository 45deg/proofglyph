From Stdlib Require Import List PeanoNat Compare_dec Lia.
From Proofglyph.Language Require Import Syntax Substitution WellFormed.
Import ListNotations.

Fixpoint locally_closed depth t : Prop :=
  match t with
  | tVar n => n < depth
  | tPi a b | tLam a b => locally_closed depth a /\ locally_closed (S depth) b
  | tApp f x => locally_closed depth f /\ locally_closed depth x
  | _ => True
  end.

Theorem typing_subject_closed sg ctx t a : typing sg ctx t a -> locally_closed (length ctx) t.
Proof.
  intros H; induction H; cbn [locally_closed] in *; auto.
  apply nth_error_Some; rewrite H; discriminate.
Qed.

Lemma rename_locally_closed t depth r q : locally_closed depth t ->
  (forall n, n < depth -> r n = q n) -> rename r t = rename q t.
Proof.
  revert depth r q; induction t; intros depth r q C E; cbn in *; try tauto;
    try (f_equal; eauto; fail).
  all: destruct C as [C D]; f_equal; [eapply IHt1; eauto|].
  all: try (eapply IHt2; [exact D|exact E]).
  all: eapply IHt2; [exact D|intros [|n] L; cbn [up_ren]; [reflexivity|f_equal; apply E; lia]].
Qed.

Lemma substitute_locally_closed t depth s q : locally_closed depth t ->
  (forall n, n < depth -> s n = q n) -> substitute s t = substitute q t.
Proof.
  revert depth s q; induction t; intros depth s q C E; cbn in *; try tauto;
    try (f_equal; eauto; fail).
  all: destruct C as [C D]; f_equal; [eapply IHt1; eauto|].
  all: try (eapply IHt2; [exact D|exact E]).
  all: eapply IHt2; [exact D|intros [|n] L; cbn [up_sub]; [reflexivity|rewrite E; [reflexivity|lia]]].
Qed.

Definition closed_signature sg := forall n a, nth_error sg n = Some a -> locally_closed 0 a.

Theorem wf_signature_closed sg : wf_signature sg -> closed_signature sg.
Proof.
  intros W; induction W; unfold closed_signature in *; intros n ty E.
  - destruct n; discriminate.
  - destruct (lt_dec n (length sg)) as [L|L].
    + rewrite nth_error_app1 in E by exact L; eauto.
    + rewrite nth_error_app2 in E by lia.
      destruct (n - length sg) as [|[|k]]; cbn in E; try discriminate.
      inversion E; subst. exact (typing_subject_closed _ _ _ _ H).
Qed.

Lemma closed_rename t r : locally_closed 0 t -> rename r t = t.
Proof.
  intros C; rewrite <- (rename_id t) at 2.
  eapply rename_locally_closed; [exact C|intros; lia].
Qed.

Lemma closed_substitute t s : locally_closed 0 t -> substitute s t = t.
Proof.
  intros C; rewrite <- (substitute_id t) at 2.
  eapply substitute_locally_closed; [exact C|intros; lia].
Qed.

Lemma shift_one t : shift 1 0 t = rename S t.
Proof. rewrite shift_as_rename; apply rename_ext; intros n; unfold shift_index; cbn; lia. Qed.

Lemma rename_lift t r : rename (up_ren r) (rename S t) = rename S (rename r t).
Proof. rewrite !rename_comp; apply rename_ext; reflexivity. Qed.

Definition renaming_context ctx dst r := forall n a, nth_error ctx n = Some a ->
  exists b, nth_error dst (r n) = Some b /\
    rename r (shift (S n) 0 a) = shift (S (r n)) 0 b.

Lemma renaming_context_up ctx dst r a : renaming_context ctx dst r ->
  renaming_context (a :: ctx) (rename r a :: dst) (up_ren r).
Proof.
  intros M [|n] ty E; cbn [nth_error up_ren] in *.
  - inversion E; subst. exists (rename r ty); split; [reflexivity|].
    rewrite !shift_one; apply rename_lift.
  - destruct (M _ _ E) as [b [LOOK EQ]]. exists b; split; [exact LOOK|].
    rewrite <- (rename_shift_succ ty (S n)), <- (rename_shift_succ b (S (r n))), rename_lift, EQ; reflexivity.
Qed.

Lemma renaming_context_weaken ctx a : renaming_context ctx (a :: ctx) S.
Proof.
  intros n ty E; exists ty; split; [exact E|apply rename_shift_succ].
Qed.

Lemma rename_sort r s : is_sort s -> rename r s = s.
Proof. intros [-> | ->]; reflexivity. Qed.
Lemma substitute_sort r s : is_sort s -> substitute r s = s.
Proof. intros [-> | ->]; reflexivity. Qed.

Theorem typing_rename sg ctx t a : closed_signature sg -> typing sg ctx t a ->
  forall dst r, renaming_context ctx dst r -> typing sg dst (rename r t) (rename r a).
Proof.
  intros CLOSED H; induction H; intros dst r M; cbn [rename].
  - constructor.
  - destruct (M _ _ H) as [b [LOOK EQ]]. rewrite EQ; apply ty_var; exact LOOK.
  - rewrite closed_rename by (eapply CLOSED; exact H); apply ty_const; exact H.
  - rewrite (rename_sort r s H1).
    eapply ty_pi; [apply IHtyping1; exact M| |exact H1].
    rewrite <- (rename_sort (up_ren r) s H1); apply IHtyping2; apply renaming_context_up; exact M.
  - eapply ty_lam with (s := s).
    + apply IHtyping1; exact M.
    + apply IHtyping2; apply renaming_context_up; exact M.
    + specialize (IHtyping3 _ _ M). cbn [rename] in IHtyping3.
      rewrite (rename_sort r s H2) in IHtyping3; exact IHtyping3.
    + exact H2.
  - rewrite rename_beta; eapply ty_app; [apply IHtyping1|apply IHtyping2]; exact M.
  - eapply ty_conv; [apply IHtyping; exact M|apply conv_rename; exact H0].
Qed.

Corollary typing_weaken sg ctx t a b : closed_signature sg -> typing sg ctx t a ->
  typing sg (b :: ctx) (rename S t) (rename S a).
Proof. intros C H; eapply typing_rename; eauto using renaming_context_weaken. Qed.

Definition typed_substitution sg ctx dst s := forall n a, nth_error ctx n = Some a ->
  typing sg dst (s n) (substitute s (shift (S n) 0 a)).

Lemma typed_substitution_up sg ctx dst s a : closed_signature sg -> typed_substitution sg ctx dst s ->
  typed_substitution sg (a :: ctx) (substitute s a :: dst) (up_sub s).
Proof.
  intros C M [|n] ty E; cbn [nth_error up_sub] in *.
  - inversion E; subst. rewrite shift_one, substitute_lift, <- shift_one.
    apply ty_var; reflexivity.
  - rewrite <- rename_shift_succ, substitute_lift.
    apply typing_weaken; [exact C|apply M; exact E].
Qed.

Theorem typing_substitute sg ctx t a : closed_signature sg -> typing sg ctx t a ->
  forall dst s, typed_substitution sg ctx dst s -> typing sg dst (substitute s t) (substitute s a).
Proof.
  intros CLOSED H; induction H; intros dst sigma M; cbn [substitute].
  - constructor.
  - apply M; exact H.
  - rewrite closed_substitute by (eapply CLOSED; exact H); apply ty_const; exact H.
  - rewrite (substitute_sort sigma s H1).
    eapply ty_pi; [apply IHtyping1; exact M| |exact H1].
    rewrite <- (substitute_sort (up_sub sigma) s H1).
    apply IHtyping2; apply typed_substitution_up; assumption.
  - eapply ty_lam with (s := s).
    + apply IHtyping1; exact M.
    + apply IHtyping2; apply typed_substitution_up; assumption.
    + specialize (IHtyping3 _ _ M); cbn [substitute] in IHtyping3.
      rewrite (substitute_sort sigma s H2) in IHtyping3; exact IHtyping3.
    + exact H2.
  - rewrite substitute_beta; eapply ty_app; [apply IHtyping1|apply IHtyping2]; exact M.
  - eapply ty_conv; [apply IHtyping; exact M|apply conv_substitute; exact H0].
Qed.

Lemma substitute_single_shift t x : substitute (single x) (rename S t) = t.
Proof.
  rewrite substitute_after_rename.
  change (substitute tVar t = t); apply substitute_id.
Qed.

Lemma typed_substitution_single sg ctx a x : typing sg ctx x a ->
  typed_substitution sg (a :: ctx) ctx (single x).
Proof.
  intros T [|n] ty E; cbn [nth_error single] in *.
  - inversion E; subst. rewrite shift_one, substitute_single_shift; exact T.
  - rewrite <- rename_shift_succ, substitute_single_shift. apply ty_var; exact E.
Qed.

Theorem typing_instantiate sg ctx a t b x :
  wf_signature sg -> typing sg (a :: ctx) t b -> typing sg ctx x a ->
  typing sg ctx (instantiate t x) (instantiate b x).
Proof.
  intros W T X; rewrite !instantiate_as_substitute.
  eapply typing_substitute; [apply wf_signature_closed; exact W|exact T|].
  apply typed_substitution_single; exact X.
Qed.

Lemma conv_substitution_pointwise t s q :
  (forall n, conv (s n) (q n)) -> conv (substitute s t) (substitute q t).
Proof.
  revert s q; induction t; intros s q C; cbn [substitute]; eauto using conv.
  - apply cv_pi; [apply IHt1; exact C|apply IHt2].
    intros [|n]; cbn [up_sub]; [apply cv_refl|apply conv_rename; apply C].
  - apply cv_lam; [apply IHt1; exact C|apply IHt2].
    intros [|n]; cbn [up_sub]; [apply cv_refl|apply conv_rename; apply C].
Qed.

Lemma conv_instantiate_argument t x y : conv x y -> conv (instantiate t x) (instantiate t y).
Proof.
  intros H; rewrite !instantiate_as_substitute; apply conv_substitution_pointwise.
  intros [|n]; cbn [single]; [exact H|apply cv_refl].
Qed.

Definition context_conv := Forall2 conv.

Lemma context_conv_lookup ctx dst n a : context_conv ctx dst -> nth_error ctx n = Some a ->
  exists b, nth_error dst n = Some b /\ conv a b.
Proof.
  intros C; revert n a; induction C; intros [|n] a E; cbn in E; try discriminate.
  - inversion E; subst; exists y; auto.
  - apply IHC; exact E.
Qed.

Lemma context_conv_refl ctx : context_conv ctx ctx.
Proof. induction ctx; constructor; auto using cv_refl. Qed.

Theorem typing_context_conversion sg ctx dst t a : wf_signature sg -> context_conv ctx dst ->
  typing sg ctx t a -> typing sg dst t a.
Proof.
  intros W C T.
  rewrite <- (substitute_id t), <- (substitute_id a).
  eapply typing_substitute; [apply wf_signature_closed; exact W|exact T|].
  intros n ty E.
  destruct (context_conv_lookup _ _ _ _ C E) as [ty' [LOOK EQ]].
  rewrite substitute_id. eapply ty_conv; [apply ty_var; exact LOOK|].
  rewrite !shift_as_rename; apply conv_rename; apply cv_sym; exact EQ.
Qed.

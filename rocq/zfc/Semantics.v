From Stdlib Require Import List Bool PeanoNat Lia.
From Proofglyph.Zfc Require Import Formula Axioms.

Section Interpretation.
Context {D : Type} (member : D -> D -> Prop).
Definition extend (x : D) (env : nat -> D) n := match n with 0 => x | S k => env k end.
Fixpoint holds (env : nat -> D) p : Prop := match p with
| Bot => False
| Equal x y => env x = env y
| Member x y => member (env x) (env y)
| Implies p q => holds env p -> holds env q
| Forall p => forall x, holds (extend x env) p
end.

Lemma holds_ext p : forall env env',
  (forall i, env i = env' i) -> (holds env p <-> holds env' p).
Proof.
  induction p; intros env env' E; cbn; try (rewrite !E; reflexivity).
  - reflexivity.
  - rewrite (IHp1 env env' E), (IHp2 env env' E); reflexivity.
  - split; intros H x.
    + apply (proj1 (IHp (extend x env) (extend x env') ltac:(intros [|i]; cbn [extend]; auto))); apply H.
    + apply (proj2 (IHp (extend x env) (extend x env') ltac:(intros [|i]; cbn [extend]; auto))); apply H.
Qed.

Lemma holds_scoped_ext p : forall n env env', scoped n p = true ->
  (forall i, i < n -> env i = env' i) -> (holds env p <-> holds env' p).
Proof.
  induction p; intros n0 env env' H E; cbn [scoped] in H; cbn [holds].
  - reflexivity.
  - apply andb_true_iff in H as [X Y]; apply Nat.ltb_lt in X; apply Nat.ltb_lt in Y.
    rewrite (E x X), (E y Y); reflexivity.
  - apply andb_true_iff in H as [X Y]; apply Nat.ltb_lt in X; apply Nat.ltb_lt in Y.
    rewrite (E x X), (E y Y); reflexivity.
  - apply andb_true_iff in H as [P Q]. rewrite (IHp1 _ _ _ P E), (IHp2 _ _ _ Q E); reflexivity.
  - assert (EX : forall x i, i < S n0 -> extend x env i = extend x env' i).
    { intros x [|i] L; cbn [extend]; [reflexivity|apply E; lia]. }
    split; intros Hx x; [apply (proj1 (IHp _ _ _ H (EX x)))|apply (proj2 (IHp _ _ _ H (EX x)))]; apply Hx.
Qed.

Theorem sentence_environment_independent p : sentence p ->
  forall env env', holds env p <-> holds env' p.
Proof. intros H env env'; eapply holds_scoped_ext; [exact H|intros; lia]. Qed.

Lemma holds_rename p : forall env rho,
  holds env (rename rho p) <-> holds (fun i => env (rho i)) p.
Proof.
  induction p; intros env rho; cbn [holds rename]; try reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - assert (E : forall x,
      holds (extend x env) (rename (up rho) p) <-> holds (extend x (fun i => env (rho i))) p).
    { intros x; rewrite IHp; apply holds_ext; intros [|i]; reflexivity. }
    split; intros H x; [apply (proj1 (E x))|apply (proj2 (E x))]; apply H.
Qed.

(** Explicit classical semantic assumption: no global logical axioms are added. *)
Context (dne : forall P : Prop, ((P -> False) -> False) -> P).

Lemma holds_and env p q : holds env (And p q) <-> holds env p /\ holds env q.
Proof.
  cbn [And Neg holds]; split.
  - intros H; split; apply dne; tauto.
  - tauto.
Qed.
Lemma holds_or env p q : holds env (Or p q) <-> holds env p \/ holds env q.
Proof.
  cbn [Or Neg holds]; split; [intros H; apply dne; tauto|tauto].
Qed.
Lemma holds_iff env p q : holds env (Iff p q) <-> (holds env p <-> holds env q).
Proof. unfold Iff; rewrite holds_and; cbn [holds]; tauto. Qed.
Lemma holds_exists env p : holds env (Exists p) <-> exists x, holds (extend x env) p.
Proof.
  cbn [Exists Neg holds]; split.
  - intros H; apply dne; intros N; apply H; intros x Px; apply N; exists x; exact Px.
  - intros [x H] N; apply (N x); exact H.
Qed.

(** Expand logical encodings uniformly, including below quantifiers. *)
Ltac semantic_connectives :=
  repeat first [progress (cbn [holds Neg extend]) | progress (setoid_rewrite holds_iff)
    | progress (setoid_rewrite holds_and)
    | progress (setoid_rewrite holds_exists)].

Theorem extensionality_meaning env : holds env extensionality <->
  forall a b, (forall x, member x a <-> member x b) -> a = b.
Proof. unfold extensionality; semantic_connectives; reflexivity. Qed.
Theorem empty_set_meaning env : holds env empty_set <->
  exists a, forall x, ~ member x a.
Proof. unfold empty_set; semantic_connectives; reflexivity. Qed.
Theorem pairing_meaning env : holds env pairing <->
  forall a b, exists p, forall x, member x p <-> x = a \/ x = b.
Proof. unfold pairing; semantic_connectives; setoid_rewrite holds_or; semantic_connectives; reflexivity. Qed.
Theorem union_meaning env : holds env union <->
  forall a, exists b, forall x, member x b <-> exists y, member y a /\ member x y.
Proof. unfold union; semantic_connectives; reflexivity. Qed.
Theorem power_set_meaning env : holds env power_set <->
  forall a, exists b, forall x, member x b <-> forall z, member z x -> member z a.
Proof. unfold power_set; semantic_connectives; reflexivity. Qed.

Theorem infinity_meaning env : holds env infinity <->
  exists i, (exists e, member e i /\ forall z, ~ member z e) /\
    forall x, member x i -> exists y, member y i /\
      forall z, member z y <-> member z x \/ z = x.
Proof. unfold infinity; semantic_connectives; setoid_rewrite holds_or; semantic_connectives; reflexivity. Qed.
Theorem foundation_meaning env : holds env foundation <->
  forall a, (exists x, member x a) -> exists x,
    member x a /\ forall y, ~ (member y x /\ member y a).
Proof. unfold foundation; semantic_connectives; reflexivity. Qed.
Theorem choice_meaning env : holds env choice <->
  forall a,
    ((forall x, member x a -> exists y, member y x) /\
     (forall x y, member x a /\ member y a /\ x <> y ->
       forall z, ~ (member z x /\ member z y))) ->
    exists c, forall x, member x a -> exists y,
      (member y x /\ member y c) /\
      forall z, member z x /\ member z c -> z = y.
Proof. unfold choice; semantic_connectives; reflexivity. Qed.

Theorem separation_body_meaning env phi :
  holds env (Forall (Exists (Forall
    (Iff (Member 0 1) (And (Member 0 2) (rename sep_ren phi)))))) <->
  forall a, exists b, forall x, member x b <-> member x a /\ holds (extend x env) phi.
Proof.
  cbn [holds]. setoid_rewrite holds_exists; cbn [holds].
  setoid_rewrite holds_iff; setoid_rewrite holds_and; cbn [holds extend].
  assert (E : forall a b x, holds (extend x (extend b (extend a env))) (rename sep_ren phi)
    <-> holds (extend x env) phi).
  { intros; rewrite holds_rename; apply holds_ext; intros [|i]; reflexivity. }
  setoid_rewrite E; reflexivity.
Qed.

Theorem replacement_body_meaning env theta :
  holds env (Forall (Implies
    (Forall (Implies (Member 0 1) (Exists
      (And (rename rep_value theta) (Forall (Implies (rename rep_unique theta) (Equal 0 1)))))))
    (Exists (Forall (Iff (Member 0 1) (Exists (And (Member 0 3) (rename rep_image theta)))))))) <->
  forall a,
    (forall x, member x a -> exists y,
      holds (extend y (extend x env)) theta /\
      forall z, holds (extend z (extend x env)) theta -> z = y) ->
    exists b, forall y, member y b <-> exists x, member x a /\ holds (extend y (extend x env)) theta.
Proof.
  cbn [holds]. setoid_rewrite holds_exists; setoid_rewrite holds_and; cbn [holds].
  setoid_rewrite holds_iff; setoid_rewrite holds_exists; setoid_rewrite holds_and;
    cbn [holds extend].
  assert (V : forall a x y, holds (extend y (extend x (extend a env))) (rename rep_value theta)
      <-> holds (extend y (extend x env)) theta).
  { intros; rewrite holds_rename; apply holds_ext; intros [|[|i]]; reflexivity. }
  assert (U : forall a x y z, holds (extend z (extend y (extend x (extend a env)))) (rename rep_unique theta)
      <-> holds (extend z (extend x env)) theta).
  { intros; rewrite holds_rename; apply holds_ext; intros [|[|i]]; reflexivity. }
  assert (I : forall a b y x, holds (extend x (extend y (extend b (extend a env)))) (rename rep_image theta)
      <-> holds (extend y (extend x env)) theta).
  { intros; rewrite holds_rename; apply holds_ext; intros [|[|i]]; reflexivity. }
  setoid_rewrite V; setoid_rewrite U; setoid_rewrite I; reflexivity.
Qed.
Fixpoint all_parameters n (P : (nat -> D) -> Prop) env := match n with
| 0 => P env
| S n => forall x, all_parameters n P (extend x env)
end.

Lemma all_parameters_ext n P Q : (forall env, P env <-> Q env) ->
  forall env, all_parameters n P env <-> all_parameters n Q env.
Proof.
  intros E; induction n; intros env; cbn [all_parameters]; [apply E|].
  split; intros H x; [apply (proj1 (IHn _))|apply (proj2 (IHn _))]; apply H.
Qed.
Lemma holds_close n p : forall env,
  holds env (close n p) <-> all_parameters n (fun rho => holds rho p) env.
Proof.
  induction n; intros env; cbn [close holds all_parameters]; [reflexivity|].
  split; intros H x; [apply (proj1 (IHn _))|apply (proj2 (IHn _))]; apply H.
Qed.

Theorem separation_meaning n phi env : holds env (separation n phi) <->
  all_parameters n (fun rho => forall a, exists b, forall x,
    member x b <-> member x a /\ holds (extend x rho) phi) env.
Proof.
  unfold separation; rewrite holds_close; apply all_parameters_ext;
    intros rho; apply separation_body_meaning.
Qed.
Theorem replacement_meaning n theta env : holds env (replacement n theta) <->
  all_parameters n (fun rho => forall a,
    (forall x, member x a -> exists y,
      holds (extend y (extend x rho)) theta /\
      forall z, holds (extend z (extend x rho)) theta -> z = y) ->
    exists b, forall y, member y b <-> exists x,
      member x a /\ holds (extend y (extend x rho)) theta) env.
Proof.
  unfold replacement; rewrite holds_close; apply all_parameters_ext;
    intros rho; apply replacement_body_meaning.
Qed.
End Interpretation.

Print Assumptions holds_rename.
Print Assumptions sentence_environment_independent.
Print Assumptions separation_body_meaning.
Print Assumptions replacement_body_meaning.

Print Assumptions separation_meaning.
Print Assumptions replacement_meaning.

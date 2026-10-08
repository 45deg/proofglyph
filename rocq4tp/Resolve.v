From Stdlib Require Import List String Arith Lia.
From Rocq4pa Require Import Syntax.
From Rocq4tp Require Import Surface.
Import ListNotations.

Definition name_eq_dec (a b : option string) : {a = b} + {a <> b}.
Proof. decide equality; apply string_dec. Defined.

Fixpoint lookup (x : string) (ns : locals) : option nat :=
  match ns with
  | [] => None
  | n :: rest =>
      if name_eq_dec n (Some x) then Some 0
      else option_map S (lookup x rest)
  end.

(** A declarative nearest-binder relation, independent of the search function. *)
Inductive binds (x : string) : locals -> nat -> Prop :=
| binds_here : forall ns, binds x (Some x :: ns) 0
| binds_later : forall n ns i,
    n <> Some x -> binds x ns i -> binds x (n :: ns) (S i).

Lemma lookup_sound x ns i : lookup x ns = Some i -> binds x ns i.
Proof.
  revert i; induction ns as [|n ns IH]; intros i H; cbn in H; [discriminate|].
  destruct (name_eq_dec n (Some x)) as [E|E].
  - subst; inversion H; constructor.
  - destruct (lookup x ns) eqn:L; inversion H; subst.
    constructor; [exact E|apply IH; reflexivity].
Qed.

Lemma lookup_complete x ns i : binds x ns i -> lookup x ns = Some i.
Proof.
  intros H; induction H; cbn -[name_eq_dec].
  - destruct (name_eq_dec (Some x) (Some x)); congruence.
  - destruct (name_eq_dec n (Some x)); [contradiction|].
    rewrite IHbinds; reflexivity.
Qed.

Lemma lookup_none x ns : lookup x ns = None <-> ~ In (Some x) ns.
Proof.
  induction ns as [|n ns IH]; cbn; [tauto|].
  destruct (name_eq_dec n (Some x)) as [E|E].
  - subst; split; [discriminate|intros H; exfalso; apply H; auto].
  - assert (N : (~ (n = Some x \/ In (Some x) ns)) <-> ~ In (Some x) ns) by tauto.
    rewrite N, <- IH.
    destruct (lookup x ns); cbn; split; intros H; congruence.
Qed.

Lemma binds_bound x ns i : binds x ns i -> i < List.length ns.
Proof. intros H; induction H; cbn; lia. Qed.

Lemma binds_append x ns i extra : binds x ns i -> binds x (ns ++ extra) i.
Proof. intros H; induction H; cbn; constructor; assumption. Qed.

Fixpoint resolve (gs : globals) (ls : locals) (e : expr) : option term :=
  match e with
  | Name x =>
      match lookup x ls with
      | Some i => Some (tVar i)
      | None => option_map tConst (lookup x (map (@Some string) gs))
      end
  | Universe => Some tType
  | Top => Some tKind
  | Apply f x =>
      match resolve gs ls f, resolve gs ls x with
      | Some f', Some x' => Some (tApp f' x') | _, _ => None end
  | Product x a b =>
      match resolve gs ls a, resolve gs (x :: ls) b with
      | Some a', Some b' => Some (tPi a' b') | _, _ => None end
  | Lambda x a b =>
      match resolve gs ls a, resolve gs (Some x :: ls) b with
      | Some a', Some b' => Some (tLam a' b') | _, _ => None end
  end.

Inductive resolves (gs : globals) : locals -> expr -> term -> Prop :=
| resolves_local : forall ls x i,
    binds x ls i -> resolves gs ls (Name x) (tVar i)
| resolves_global : forall ls x i,
    ~ In (Some x) ls -> binds x (map (@Some string) gs) i ->
    resolves gs ls (Name x) (tConst i)
| resolves_type : forall ls, resolves gs ls Universe tType
| resolves_kind : forall ls, resolves gs ls Top tKind
| resolves_app : forall ls f x f' x',
    resolves gs ls f f' -> resolves gs ls x x' ->
    resolves gs ls (Apply f x) (tApp f' x')
| resolves_pi : forall ls x a b a' b',
    resolves gs ls a a' -> resolves gs (x :: ls) b b' ->
    resolves gs ls (Product x a b) (tPi a' b')
| resolves_lam : forall ls x a b a' b',
    resolves gs ls a a' -> resolves gs (Some x :: ls) b b' ->
    resolves gs ls (Lambda x a b) (tLam a' b').

Theorem resolve_sound gs ls e t : resolve gs ls e = Some t -> resolves gs ls e t.
Proof.
  revert ls t; induction e; intros ls t H; cbn in H.
  - destruct (lookup x ls) eqn:L.
    + inversion H; subst; constructor; apply lookup_sound; exact L.
    + destruct (lookup x (map (@Some string) gs)) eqn:G; inversion H; subst.
      apply resolves_global; [apply lookup_none; exact L|apply lookup_sound; exact G].
  - inversion H; constructor.
  - inversion H; constructor.
  - destruct (resolve gs ls e1) eqn:A; [|discriminate].
    destruct (resolve gs ls e2) eqn:B; inversion H; subst; constructor; auto.
  - destruct (resolve gs ls e1) eqn:A; [|discriminate].
    destruct (resolve gs (x :: ls) e2) eqn:B; inversion H; subst; constructor; auto.
  - destruct (resolve gs ls e1) eqn:A; [|discriminate].
    destruct (resolve gs (Some x :: ls) e2) eqn:B; inversion H; subst; constructor; auto.
Qed.

Theorem resolve_complete gs ls e t : resolves gs ls e t -> resolve gs ls e = Some t.
Proof.
  intros H; induction H; cbn; try rewrite IHresolves1, IHresolves2; try reflexivity.
  - rewrite (lookup_complete _ _ _ H); reflexivity.
  - rewrite (proj2 (lookup_none _ _) H), (lookup_complete _ _ _ H0); reflexivity.
Qed.

Theorem resolve_correct gs ls e t : resolve gs ls e = Some t <-> resolves gs ls e t.
Proof. split; [apply resolve_sound|apply resolve_complete]. Qed.

Theorem resolves_unique gs ls e t u :
  resolves gs ls e t -> resolves gs ls e u -> t = u.
Proof. intros A B; apply resolve_complete in A; apply resolve_complete in B; congruence. Qed.

Theorem resolves_extend_globals gs ls e t extra :
  resolves gs ls e t -> resolves (gs ++ extra) ls e t.
Proof.
  intros H; induction H.
  - constructor; assumption.
  - apply resolves_global; [assumption|].
    rewrite map_app; apply binds_append; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Fixpoint scoped (constants depth : nat) (t : term) : Prop :=
  match t with
  | tVar i => i < depth
  | tConst i => i < constants
  | tPi a b | tLam a b => scoped constants depth a /\ scoped constants (S depth) b
  | tApp f x => scoped constants depth f /\ scoped constants depth x
  | _ => True
  end.

Theorem resolves_scoped gs ls e t :
  resolves gs ls e t -> scoped (List.length gs) (List.length ls) t.
Proof.
  intros H; induction H; cbn in *.
  - eapply binds_bound; eauto.
  - match goal with B : binds _ (map _ _) _ |- _ =>
      pose proof (binds_bound _ _ _ B) as L; rewrite length_map in L; exact L end.
  - exact I.
  - exact I.
  - auto.
  - auto.
  - auto.
Qed.

Corollary resolve_scoped gs ls e t :
  resolve gs ls e = Some t -> scoped (List.length gs) (List.length ls) t.
Proof. intros H; apply resolves_scoped with (e := e); apply resolve_sound; exact H. Qed.

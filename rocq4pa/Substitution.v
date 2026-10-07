From Stdlib Require Import List PeanoNat Lia.
From Rocq4pa Require Import Syntax.

Definition up_ren (r : nat -> nat) n := match n with 0 => 0 | S k => S (r k) end.

Fixpoint rename (r : nat -> nat) t :=
  match t with
  | tVar n => tVar (r n)
  | tPi a b => tPi (rename r a) (rename (up_ren r) b)
  | tLam a b => tLam (rename r a) (rename (up_ren r) b)
  | tApp f x => tApp (rename r f) (rename r x)
  | _ => t
  end.

Lemma rename_ext t r q : (forall n, r n = q n) -> rename r t = rename q t.
Proof.
  revert r q; induction t; intros r q E; cbn; f_equal; eauto.
  all: apply IHt2; intros [|n]; cbn [up_ren]; auto.
Qed.

Lemma rename_id t : rename (fun n => n) t = t.
Proof.
  induction t; cbn; try (f_equal; auto; fail).
  all: f_equal; auto; rewrite <- IHt2 at 2; apply rename_ext; intros [|n]; reflexivity.
Qed.

Lemma rename_comp t r q : rename q (rename r t) = rename (fun n => q (r n)) t.
Proof.
  revert r q; induction t; intros; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1|rewrite IHt2; apply rename_ext; intros [|n]; reflexivity].
Qed.

Definition up_sub (s : nat -> term) n :=
  match n with 0 => tVar 0 | S k => rename S (s k) end.

Fixpoint substitute (s : nat -> term) t :=
  match t with
  | tVar n => s n
  | tPi a b => tPi (substitute s a) (substitute (up_sub s) b)
  | tLam a b => tLam (substitute s a) (substitute (up_sub s) b)
  | tApp f x => tApp (substitute s f) (substitute s x)
  | _ => t
  end.

Lemma substitute_ext t s q : (forall n, s n = q n) -> substitute s t = substitute q t.
Proof.
  revert s q; induction t; intros s q E; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1; exact E|apply IHt2; intros [|n]; cbn [up_sub]; auto; rewrite E; reflexivity].
Qed.

Lemma substitute_rename t r : substitute (fun n => tVar (r n)) t = rename r t.
Proof.
  revert r; induction t; intros r; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1|rewrite <- IHt2; apply substitute_ext; intros [|n]; reflexivity].
Qed.

Lemma substitute_id t : substitute tVar t = t.
Proof. change (substitute (fun n => tVar n) t = t). rewrite substitute_rename, rename_id; reflexivity. Qed.

Lemma rename_substitute t s r :
  rename r (substitute s t) = substitute (fun n => rename r (s n)) t.
Proof.
  revert s r; induction t; intros s r; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1|rewrite IHt2; apply substitute_ext; intros [|n]; cbn [up_sub rename]].
  all: try reflexivity; rewrite !rename_comp; apply rename_ext; reflexivity.
Qed.

Lemma substitute_after_rename t r s :
  substitute s (rename r t) = substitute (fun n => s (r n)) t.
Proof.
  revert r s; induction t; intros r s; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1|rewrite IHt2; apply substitute_ext; intros [|n]; reflexivity].
Qed.

Lemma substitute_lift t s :
  substitute (up_sub s) (rename S t) = rename S (substitute s t).
Proof. rewrite substitute_after_rename, rename_substitute; reflexivity. Qed.

Lemma substitute_comp t s q :
  substitute q (substitute s t) = substitute (fun n => substitute q (s n)) t.
Proof.
  revert s q; induction t; intros s q; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1|rewrite IHt2; apply substitute_ext; intros [|n]; cbn [up_sub substitute]].
  all: try reflexivity; apply substitute_lift.
Qed.

Definition shift_index delta cutoff n := if cutoff <=? n then n + delta else n.

Lemma shift_as_rename t delta cutoff : shift delta cutoff t = rename (shift_index delta cutoff) t.
Proof.
  revert cutoff; induction t; intros cutoff; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1|rewrite IHt2; apply rename_ext; intros [|n]; unfold shift_index, up_ren].
  all: cbn; try reflexivity; destruct (cutoff <=? n); reflexivity.
Qed.

Lemma rename_shift_succ t depth : rename S (shift depth 0 t) = shift (S depth) 0 t.
Proof.
  rewrite !shift_as_rename, rename_comp; apply rename_ext.
  intros n; unfold shift_index; cbn; lia.
Qed.

Definition replace_index depth value n :=
  if n =? depth then shift depth 0 value
  else tVar (if depth <? n then pred n else n).

Lemma replace_index_up depth value n :
  replace_index (S depth) value n = up_sub (replace_index depth value) n.
Proof.
  destruct n as [|n]; [reflexivity|].
  change ((if n =? depth then shift (S depth) 0 value
           else tVar (if depth <? n then n else S n)) =
          rename S (if n =? depth then shift depth 0 value
           else tVar (if depth <? n then pred n else n))).
  destruct (n =? depth) eqn:E.
  - symmetry; apply rename_shift_succ.
  - destruct (depth <? n) eqn:L; cbn [rename]; [apply Nat.ltb_lt in L; destruct n; [lia|reflexivity]|reflexivity].
Qed.

Lemma subst_as_substitute t depth value : subst depth value t = substitute (replace_index depth value) t.
Proof.
  revert depth; induction t; intros depth; cbn; try (f_equal; eauto; fail).
  all: f_equal; [apply IHt1|rewrite IHt2; apply substitute_ext; apply replace_index_up].
Qed.

Definition single value n := match n with 0 => value | S k => tVar k end.

Lemma instantiate_as_substitute t value : instantiate t value = substitute (single value) t.
Proof.
  unfold instantiate; rewrite subst_as_substitute; apply substitute_ext.
  intros [|n]; unfold replace_index, single; cbn; [|reflexivity].
  rewrite shift_as_rename; transitivity (rename (fun n => n) value).
  - apply rename_ext; intros k; unfold shift_index; cbn; lia.
  - apply rename_id.
Qed.

Lemma substitute_beta body value s :
  substitute s (instantiate body value) =
  instantiate (substitute (up_sub s) body) (substitute s value).
Proof.
  rewrite !instantiate_as_substitute, !substitute_comp; apply substitute_ext.
  intros [|n]; cbn [single up_sub substitute]; [reflexivity|].
  rewrite substitute_after_rename.
  change (s n = substitute tVar (s n)); symmetry; apply substitute_id.
Qed.

Theorem conv_substitute a b s : conv a b -> conv (substitute s a) (substitute s b).
Proof.
  intros H; revert s; induction H; intros s; cbn [substitute]; eauto using conv.
  rewrite substitute_beta; apply cv_beta.
Qed.

Theorem conv_rename a b r : conv a b -> conv (rename r a) (rename r b).
Proof.
  intros H; rewrite <- !substitute_rename; apply conv_substitute; exact H.
Qed.

Lemma rename_beta body value r :
  rename r (instantiate body value) =
  instantiate (rename (up_ren r) body) (rename r value).
Proof.
  rewrite <- !substitute_rename, substitute_beta; f_equal.
  apply substitute_ext; intros [|n]; reflexivity.
Qed.

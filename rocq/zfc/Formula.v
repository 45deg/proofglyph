From Stdlib Require Import List PeanoNat Bool.
Import ListNotations.

(** Pure first-order set-theory syntax: variables are de Bruijn indices;
    there are no function symbols or higher-order predicate parameters. *)
Inductive formula :=
| Bot
| Equal (x y : nat)
| Member (x y : nat)
| Implies (p q : formula)
| Forall (p : formula).

Definition Neg p := Implies p Bot.
Definition Or p q := Implies (Neg p) q.
Definition And p q := Neg (Implies p (Neg q)).
Definition Exists p := Neg (Forall (Neg p)).
Definition Iff p q := And (Implies p q) (Implies q p).

Fixpoint scoped (depth : nat) (p : formula) : bool :=
  match p with
  | Bot => true
  | Equal x y | Member x y => (x <? depth) && (y <? depth)
  | Implies p q => scoped depth p && scoped depth q
  | Forall p => scoped (S depth) p
  end.
Definition sentence p := scoped 0 p = true.

Fixpoint lift (cutoff amount : nat) (p : formula) : formula :=
  let index n := if cutoff <=? n then n + amount else n in
  match p with
  | Bot => Bot
  | Equal x y => Equal (index x) (index y)
  | Member x y => Member (index x) (index y)
  | Implies p q => Implies (lift cutoff amount p) (lift cutoff amount q)
  | Forall p => Forall (lift (S cutoff) amount p)
  end.

(** Three initial ZFC sentences, independently of the proofglyph checker. *)
Definition extensionality :=
  Forall (Forall (Implies
    (Forall (Iff (Member 0 2) (Member 0 1))) (Equal 1 0))).
Definition empty_set := Exists (Forall (Neg (Member 0 1))).
Definition pairing := Forall (Forall (Exists (Forall
  (Iff (Member 0 1) (Or (Equal 0 3) (Equal 0 2)))))).

Example extensionality_closed : sentence extensionality.
Proof. reflexivity. Qed.
Example empty_set_closed : sentence empty_set.
Proof. reflexivity. Qed.
Example pairing_closed : sentence pairing.
Proof. reflexivity. Qed.
Example free_variable_rejected : scoped 0 (Member 0 1) = false.
Proof. reflexivity. Qed.
Example bound_variable_accepted : sentence (Forall (Member 0 0)).
Proof. reflexivity. Qed.

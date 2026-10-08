From Stdlib Require Import List Bool.
From Tinyprover.Pa Require Export Syntax.
Import ListNotations.

Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with Some a => f a | None => None end.
Notation "x <- c ;; f" := (bind c (fun x => f))
  (at level 100, c at next level, right associativity).

(** Fuel bounds recursion depth, not total work. Exhaustion never succeeds. *)
Fixpoint normal (fuel : nat) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S n =>
    match t with
    | tPi a b => a' <- normal n a ;; b' <- normal n b ;; Some (tPi a' b')
    | tLam a b => a' <- normal n a ;; b' <- normal n b ;; Some (tLam a' b')
    | tApp f x =>
      f' <- normal n f ;; x' <- normal n x ;;
      match f' with
      | tLam a b => normal n (instantiate b x')
      | _ => Some (tApp f' x')
      end
    | _ => Some t
    end
  end.

Definition equal (fuel : nat) (a b : term) : bool :=
  match normal fuel a, normal fuel b with
  | Some a', Some b' => if term_eq_dec a' b' then true else false
  | _, _ => false
  end.

Definition as_sort fuel a : option term :=
  s <- normal fuel a ;; if sortb s then Some s else None.


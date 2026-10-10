From Stdlib Require Import List Bool.
From Proofglyph.Language Require Export KernelImpl.

(** Fuel bounds recursion depth. Lambda bodies and arguments remain untouched. *)
Fixpoint whnf fuel t : option term := match fuel with
| 0 => None
| S n => match t with
  | tApp f x => f' <- whnf n f ;;
      match f' with
      | tLam a b => whnf n (instantiate b x)
      | _ => Some (tApp f' x)
      end
  | _ => Some t
  end
end.

Fixpoint w_equal fuel a b : bool :=
  if term_eq_dec a b then true else match fuel with
  | 0 => false
  | S n => match whnf n a, whnf n b with
    | Some u, Some v => if term_eq_dec u v then true else
      match u, v with
      | tPi a b, tPi c d | tLam a b, tLam c d | tApp a b, tApp c d =>
          w_equal n a c && w_equal n b d
      | _, _ => false
      end
    | _, _ => false
    end
  end.

Definition w_as_sort fuel a : option term :=
  s <- whnf fuel a ;; if sortb s then Some s else None.

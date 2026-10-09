From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Tinyprover.Hieratic Require Export ResolveSpec.

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


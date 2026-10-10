From Stdlib Require Import List.
Import ListNotations.

(** A finite, persistent table. Extraction replaces this representation and
    these three operations together; proofs do not assume a hash implementation. *)
Inductive table (K V : Type) := Table (entries : list (K * V)).
Arguments Table {K V} _.
Definition table_empty {K V} (_ : unit) : table K V := Table [].
Fixpoint list_lookup {K V} (eq : forall a b : K, {a = b} + {a <> b})
  (key : K) (entries : list (K * V)) : option V :=
  match entries with
  | [] => None
  | (k, v) :: rest => if eq key k then Some v else list_lookup eq key rest
  end.
Definition table_lookup {K V} eq key (t : table K V) :=
  match t with Table entries => list_lookup eq key entries end.
Definition table_insert {K V} (key : K) (value : V) (t : table K V) :=
  match t with Table entries => Table ((key, value) :: entries) end.

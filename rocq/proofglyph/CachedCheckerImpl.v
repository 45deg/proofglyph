From Stdlib Require Import List Bool PeanoNat.
From Proofglyph.Language Require Export WeakCheckerImpl CacheTableImpl.
Import ListNotations.

Definition cache_key := (list term * term)%type.
Definition cache_value := (nat * term)%type.
Definition inference_table := table cache_key cache_value.
Definition cache_key_eq (a b : cache_key) : {a = b} + {a <> b}.
Proof. decide equality; [apply term_eq_dec|apply list_eq_dec; apply term_eq_dec]. Defined.

(** Only successful results are stored. A hit is reusable only if its recorded
    depth bound fits the current fuel, preserving the uncached fuel contract. *)
Definition memoize fuel key (cache : inference_table)
  (compute : inference_table -> option (term * inference_table)) :=
  let fresh := fun _ : unit =>
    result <- compute cache ;;
    let '(a, next) := result in
    Some (a, table_insert key (fuel, a) next) in
  match table_lookup cache_key_eq key cache with
  | Some (bound, a) => if bound <=? fuel then Some (a, cache) else fresh tt
  | None => fresh tt
  end.

Fixpoint infer fuel sg ctx t (cache : inference_table) : option (term * inference_table) :=
  match fuel with
  | 0 => None
  | S n => memoize (S n) (ctx, t) cache (fun cache => match t with
    | tType => Some (tKind, cache)
    | tKind => None
    | tVar i => a <- nth_error ctx i ;; Some (shift (S i) 0 a, cache)
    | tConst i => a <- nth_error sg i ;; Some (a, cache)
    | tPi a b =>
      result <- infer n sg ctx a cache ;;
      let '(aty, next) := result in
      match w_as_sort n aty with Some tType =>
        result <- infer n sg (a :: ctx) b next ;;
        let '(bt, next) := result in
        s <- w_as_sort n bt ;; Some (s, next)
      | _ => None end
    | tLam a b =>
      result <- infer n sg ctx a cache ;;
      let '(aty, next) := result in
      match w_as_sort n aty with Some tType =>
        result <- infer n sg (a :: ctx) b next ;;
        let '(bt, next) := result in
        match bt with tKind => None | _ => Some (tPi a bt, next) end
      | _ => None end
    | tApp f x =>
      result <- infer n sg ctx f cache ;;
      let '(ft, next) := result in
      p <- whnf n ft ;;
      match p with
      | tPi a b => result <- infer n sg ctx x next ;;
        let '(xt, next) := result in
        if w_equal n xt a then Some (instantiate b x, next) else None
      | _ => None end
    end)
  end.

Definition check fuel sg t a : bool :=
  match infer fuel sg [] a (table_empty tt) with
  | Some (aty, cache) => match infer fuel sg [] t cache with
    | Some (actual, _) => match w_as_sort fuel aty with
      | Some _ => w_equal fuel actual a | None => false end
    | None => false end
  | None => false end.

Definition check_declaration fuel (allow : bool) sg d := match d with
| Assume a => if allow then
    match infer fuel sg [] a (table_empty tt) with
    | Some (aty, _) => match w_as_sort fuel aty with Some _ => true | None => false end
    | None => false end else false
| Prove a t => check fuel sg t a
end.

(** Every declaration starts with a fresh table; signature-dependent results
    cannot survive registration or cross the prelude/main boundary. *)
Fixpoint check_program fuel allow sg ds : option (list term) := match ds with
| [] => Some sg
| d :: rest => if check_declaration fuel allow sg d then
    check_program fuel allow (sg ++ [declared_type d]) rest else None
end.

From Stdlib Require Import List Bool.
From Tinyprover.Pa Require Export Syntax Program KernelImpl.
Import ListNotations.

Fixpoint infer fuel sg ctx t : option term :=
  match fuel with
  | 0 => None
  | S n => match t with
    | tType => Some tKind
    | tKind => None
    | tVar i => a <- nth_error ctx i ;; Some (shift (S i) 0 a)
    | tConst i => nth_error sg i
    | tPi a b =>
      aty <- infer n sg ctx a ;;
      if equal n aty tType then
        bt <- infer n sg (a :: ctx) b ;; as_sort n bt
      else None
    | tLam a b =>
      aty <- infer n sg ctx a ;;
      if equal n aty tType then
        bt <- infer n sg (a :: ctx) b ;;
        match bt with tKind => None | _ => Some (tPi a bt) end
      else None
    | tApp f x =>
      ft <- infer n sg ctx f ;; p <- normal n ft ;;
      match p with
      | tPi a b => xt <- infer n sg ctx x ;;
        if equal n xt a then Some (instantiate b x) else None
      | _ => None
      end
    end
  end.

Definition check fuel sg t a : bool :=
  match infer fuel sg [] a, infer fuel sg [] t with
  | Some aty, Some actual =>
    match as_sort fuel aty with Some _ => equal fuel actual a | None => false end
  | _, _ => false
  end.

Definition check_declaration fuel (allow : bool) sg d :=
  match d with
  | Assume a => if allow then
      match infer fuel sg [] a with
      | Some aty => match as_sort fuel aty with Some _ => true | None => false end
      | None => false end else false
  | Prove a t => check fuel sg t a
  end.

Fixpoint check_program fuel allow sg ds : option (list term) :=
  match ds with
  | [] => Some sg
  | d :: rest => if check_declaration fuel allow sg d then
      check_program fuel allow (sg ++ [declared_type d]) rest else None
  end.


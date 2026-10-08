From Stdlib Require Import List String.
From Rocq4tp Require Import Desugar TpSyntax.
Import ListNotations.
Open Scope nat_scope.

(** The host supplies a finite table indexed by canonical file identities.
    Import targets in this table have already been resolved by the host. *)
Definition tp_files := list (string * list tp_item).
Definition contains_file p := existsb (String.eqb p).
Fixpoint lookup_file p (files : tp_files) :=
  match files with
  | [] => None
  | (q,items)::rest => if String.eqb p q then Some items else lookup_file p rest
  end.
Fixpoint visit_tp fuel files active seen path : option (list raw_declaration * list string) :=
  match fuel with
  | 0 => None
  | S k => if contains_file path active then None else
      if contains_file path seen then Some ([],seen) else
      match lookup_file path files with
      | None => None
      | Some items => match expand_tp_items k files (path::active) seen items with
        | Some (ds,seen) => Some (ds,path::seen) | None => None end
      end
  end
with expand_tp_items fuel files active seen items : option (list raw_declaration * list string) :=
  match fuel with
  | 0 => None
  | S k => match items with
    | [] => Some ([],seen)
    | TpDeclaration d :: rest =>
        match expand_tp_items k files active seen rest with
        | Some (ds,seen) => Some (d::ds,seen) | None => None end
    | TpImport p :: rest => match visit_tp k files active seen p with
        | Some (ds,seen) => match expand_tp_items k files active seen rest with
          | Some (tail,seen) => Some (List.app ds tail,seen) | None => None end
        | None => None end
    end
  end.
Definition import_budget (files : tp_files) :=
  S (2 * fold_right (fun f n => S (List.length (snd f)) + n) 0 files).
Definition load_tp files entry :=
  option_map fst (visit_tp (import_budget files) files [] [] entry).

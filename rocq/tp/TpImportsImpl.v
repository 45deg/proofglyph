From Stdlib Require Import List String.
From Tinyprover.Tp Require Export TpImportsSpec.
From Tinyprover.Tp Require Export TpSyntaxSpec.
Import ListNotations.
Open Scope list_scope.
Open Scope nat_scope.

Definition contains_file p := existsb (String.eqb p).
Fixpoint lookup_file p (files : tp_files) :=
  match files with
  | [] => None
  | (q,items)::rest => if String.eqb p q then Some items else lookup_file p rest
  end.

(** Item traversal is structural. Only entering a file consumes depth fuel. *)
Fixpoint expand_items_with
    (walk : list string -> string -> option (list raw_declaration * list string))
    items seen : option (list raw_declaration * list string) :=
  match items with
  | [] => Some ([],seen)
  | TpDeclaration d::rest =>
      match expand_items_with walk rest seen with
      | Some (ds,done) => Some (d::ds,done) | None => None end
  | TpImport p::rest => match walk seen p with
      | Some (ds,mid) => match expand_items_with walk rest mid with
          | Some (tail,done) => Some (ds++tail,done) | None => None end
      | None => None end
  end.
Fixpoint visit_tp fuel files active seen path : option (list raw_declaration * list string) :=
  match fuel with
  | 0 => None
  | S k => if contains_file path active then None else
      if contains_file path seen then Some ([],seen) else
      match lookup_file path files with
      | None => None
      | Some items =>
          match expand_items_with (fun seen p => visit_tp k files (path::active) seen p) items seen with
          | Some (ds,done) => Some (ds,path::done) | None => None end
      end
  end.
Definition expand_tp_items fuel files active seen items :=
  expand_items_with (fun seen p => visit_tp fuel files active seen p) items seen.
Definition import_budget (files : tp_files) := S (List.length files).
Definition load_tp files entry := option_map fst (visit_tp (import_budget files) files [] [] entry).

From Stdlib Require Import List String Arith Lia.
From Tinyprover.Tp Require Export DesugarSpec.
From Tinyprover.Tp Require Export TpSyntaxSpec.
Import ListNotations.
Open Scope list_scope.

Definition tp_files := list (string * list tp_item).
(** First matching entry; canonical host tables have unique keys. *)
Inductive file_entry (p : string) : tp_files -> list tp_item -> Prop :=
| file_here : forall items rest, file_entry p ((p,items)::rest) items
| file_later : forall q items rest found,
    p <> q -> file_entry p rest found -> file_entry p ((q,items)::rest) found.

(** Fuel-free depth-first expansion, with declaration-position imports and
    one expansion per file. Active paths take precedence over completed ones. *)
Inductive visits (files : tp_files) : list string -> list string -> string ->
    list raw_declaration -> list string -> Prop :=
| visits_seen : forall active seen path,
    ~ In path active -> In path seen -> visits files active seen path [] seen
| visits_new : forall active seen path items ds done,
    ~ In path active -> ~ In path seen -> file_entry path files items ->
    expands_items files (path::active) seen items ds done ->
    visits files active seen path ds (path::done)
with expands_items (files : tp_files) : list string -> list string -> list tp_item ->
    list raw_declaration -> list string -> Prop :=
| items_nil : forall active seen, expands_items files active seen [] [] seen
| items_decl : forall active seen d rest ds done,
    expands_items files active seen rest ds done ->
    expands_items files active seen (TpDeclaration d::rest) (d::ds) done
| items_import : forall active seen path rest ds mid tail done,
    visits files active seen path ds mid ->
    expands_items files active mid rest tail done ->
    expands_items files active seen (TpImport path::rest) (ds++tail) done.
Scheme visits_ind' := Induction for visits Sort Prop
with expands_items_ind' := Induction for expands_items Sort Prop.
Combined Scheme imports_ind from visits_ind', expands_items_ind'.
Definition imports_program files entry ds := exists done, visits files [] [] entry ds done.

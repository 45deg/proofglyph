From Stdlib Require Import List String.
From Tinyprover.Pa Require Export Syntax Program WellFormed CodecSpec.
From Tinyprover.Tp Require Export TpImportsSpec CompileSpec.
Import ListNotations.
Open Scope list_scope.

(** The host supplies an immutable byte snapshot and canonical import targets.
    Resolving path spellings and reading bytes remain outside the theorem. *)
Definition file_inputs := list (string * string).
Definition path_resolver := string -> string -> option string.
Inductive canonical_items (resolve : path_resolver) (origin : string) :
    list tp_item -> list tp_item -> Prop :=
| canonical_nil : canonical_items resolve origin [] []
| canonical_decl : forall d items canonical,
    canonical_items resolve origin items canonical ->
    canonical_items resolve origin (TpDeclaration d::items) (TpDeclaration d::canonical)
| canonical_import : forall spelling target items canonical,
    resolve origin spelling = Some target -> canonical_items resolve origin items canonical ->
    canonical_items resolve origin (TpImport spelling::items) (TpImport target::canonical).
Inductive parsed_files (resolve : path_resolver) : file_inputs -> tp_files -> Prop :=
| parsed_nil : parsed_files resolve [] []
| parsed_cons : forall path bytes items canonical inputs files,
    tp_parses bytes items -> canonical_items resolve path items canonical ->
    parsed_files resolve inputs files ->
    parsed_files resolve ((path,bytes)::inputs) ((path,canonical)::files).
Definition files_spec resolve inputs entry allow bytes sg :=
  exists files raw src ds,
    parsed_files resolve inputs files /\ imports_program files entry raw /\
    expands_program raw src /\ translates [] src ds /\ source_permitted allow src /\
    valid_program [] ds sg /\ pa_decodes bytes ds.

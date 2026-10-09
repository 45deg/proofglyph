From Stdlib Require Import List String.
From Tinyprover.Proofglyph Require Export Syntax Program WellFormed CodecSpec.
From Tinyprover.Hieratic Require Export HieraticImportsSpec CompileSpec.
Import ListNotations.
Open Scope list_scope.

(** The host supplies an immutable byte snapshot and canonical import targets.
    Resolving path spellings and reading bytes remain outside the theorem. *)
Definition file_inputs := list (string * string).
Definition path_resolver := string -> string -> option string.
Inductive canonical_items (resolve : path_resolver) (origin : string) :
    list hieratic_item -> list hieratic_item -> Prop :=
| canonical_nil : canonical_items resolve origin [] []
| canonical_decl : forall d items canonical,
    canonical_items resolve origin items canonical ->
    canonical_items resolve origin (HieraticDeclaration d::items) (HieraticDeclaration d::canonical)
| canonical_import : forall spelling target items canonical,
    resolve origin spelling = Some target -> canonical_items resolve origin items canonical ->
    canonical_items resolve origin (HieraticImport spelling::items) (HieraticImport target::canonical).
Inductive parsed_files (resolve : path_resolver) : file_inputs -> hieratic_files -> Prop :=
| parsed_nil : parsed_files resolve [] []
| parsed_cons : forall path bytes items canonical inputs files,
    hieratic_parses bytes items -> canonical_items resolve path items canonical ->
    parsed_files resolve inputs files ->
    parsed_files resolve ((path,bytes)::inputs) ((path,canonical)::files).
Definition files_spec resolve inputs entry allow bytes sg :=
  exists files raw src ds,
    parsed_files resolve inputs files /\ imports_program files entry raw /\
    expands_program raw src /\ translates [] src ds /\ source_permitted allow src /\
    valid_program [] ds sg /\ proofglyph_decodes bytes ds.

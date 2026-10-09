From Stdlib Require Import List String.
From Proofglyph.Language Require Import Syntax.
From Proofglyph.Hieratic Require Import FileCompile.
Import ListNotations.
Open Scope string_scope.

Definition same_path (_ path : string) := Some path.
Definition files_identity :=
  [("entry", "import ""base""; def id (x : A) : A := x;");
   ("base", "axiom A : Type;")].
Example bytes_to_checked_proofglyph : compile_files_proofglyph 64 true same_path files_identity "entry" =
  Some ("*:#0#0>#0$0\!", [tType;tPi (tConst 0) (tConst 0)]).
Proof. vm_compute; reflexivity. Qed.
Example bytes_to_checked_declarations : compile_files 64 true same_path files_identity "entry" =
  Some ([Assume tType; Prove (tPi (tConst 0) (tConst 0)) (tLam (tConst 0) (tVar 0))],
    [tType;tPi (tConst 0) (tConst 0)]).
Proof. vm_compute; reflexivity. Qed.
Example unresolved_spelling : prepare_files (fun _ _ => None) files_identity = None.
Proof. vm_compute; reflexivity. Qed.
Example missing_target : compile_files_proofglyph 64 true same_path
  [("entry","import ""absent"";")] "entry" = None.
Proof. vm_compute; reflexivity. Qed.
Example cyclic_bytes : compile_files_proofglyph 64 true same_path
  [("a","import ""b"";");("b","import ""a"";")] "a" = None.
Proof. vm_compute; reflexivity. Qed.
Example byte_policy : compile_files_proofglyph 64 false same_path files_identity "entry" = None.
Proof. vm_compute; reflexivity. Qed.
Example byte_fuel : compile_files_proofglyph 1 true same_path files_identity "entry" = None.
Proof. vm_compute; reflexivity. Qed.
Example invalid_unused_file : prepare_files same_path
  [("entry","");("unused","axiom A : ;")] = None.
Proof. vm_compute; reflexivity. Qed.
Example empty_files_entry : compile_files_proofglyph 64 false same_path [("entry","")] "entry" = Some ("",[]).
Proof. vm_compute; reflexivity. Qed.

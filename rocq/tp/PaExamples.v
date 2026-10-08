From Stdlib Require Import List String Ascii.
From Tinyprover.Pa Require Import Syntax Program.
From Tinyprover.Tp Require Import PaCodec PaCompile Examples.
Import ListNotations.
Open Scope string_scope.

Example identity_bytes : encode_pa
  [Assume tType; Prove (tPi (tConst 0) (tConst 0)) (tLam (tConst 0) (tVar 0))] =
  "*:#0#0>#0$0\!".
Proof. reflexivity. Qed.

Example multidigit_and_leading_zeroes : decode_pa "$0012#345@:" =
  Some [Assume (tApp (tVar 12) (tConst 345))].
Proof. reflexivity. Qed.

Example whitespace_between_tokens : decode_pa
  (String "009" ("*" ++ String "010" (String "013" " : "))) = Some [Assume tType].
Proof. reflexivity. Qed.

Example whitespace_inside_index_rejected : decode_pa "# 0:" = None.
Proof. reflexivity. Qed.

Example missing_index_rejected : decode_pa "#:" = None.
Proof. reflexivity. Qed.

Example negative_index_rejected : decode_pa "#-1:" = None.
Proof. reflexivity. Qed.

Example unknown_byte_rejected : decode_pa "*:?" = None.
Proof. reflexivity. Qed.

Example stack_underflow_rejected : decode_pa "*>:" = None.
Proof. reflexivity. Qed.

Example excess_assumption_stack_rejected : decode_pa "**:" = None.
Proof. reflexivity. Qed.

Example excess_proof_stack_rejected : decode_pa "***!" = None.
Proof. reflexivity. Qed.

Example unfinished_stack_rejected : decode_pa "*:*" = None.
Proof. reflexivity. Qed.

Example raw_decode_does_not_check_types : decode_pa "^:" = Some [Assume tKind].
Proof. reflexivity. Qed.

Example checked_decode_rejects_bad_type : check_pa 32 true "^:" = None.
Proof. reflexivity. Qed.

Example compile_identity_to_bytes : compile_pa 32 true identity_source =
  Some ("*:#0#0>#0$0\!", [tType; tPi (tConst 0) (tConst 0)]).
Proof. reflexivity. Qed.

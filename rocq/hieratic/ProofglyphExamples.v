From Stdlib Require Import List String Ascii.
From Tinyprover.Proofglyph Require Import Syntax Program.
From Tinyprover.Hieratic Require Import ProofglyphCodec ProofglyphCompile Examples.
Import ListNotations.
Open Scope string_scope.

Example identity_bytes : encode_proofglyph
  [Assume tType; Prove (tPi (tConst 0) (tConst 0)) (tLam (tConst 0) (tVar 0))] =
  "*:#0#0>#0$0\!".
Proof. reflexivity. Qed.

Example multidigit_and_leading_zeroes : decode_proofglyph "$0012#345@:" =
  Some [Assume (tApp (tVar 12) (tConst 345))].
Proof. reflexivity. Qed.

Example whitespace_between_tokens : decode_proofglyph
  (String "009" ("*" ++ String "010" (String "013" " : "))) = Some [Assume tType].
Proof. reflexivity. Qed.

Example whitespace_inside_index_rejected : decode_proofglyph "# 0:" = None.
Proof. reflexivity. Qed.

Example missing_index_rejected : decode_proofglyph "#:" = None.
Proof. reflexivity. Qed.

Example negative_index_rejected : decode_proofglyph "#-1:" = None.
Proof. reflexivity. Qed.

Example unknown_byte_rejected : decode_proofglyph "*:?" = None.
Proof. reflexivity. Qed.

Example stack_underflow_rejected : decode_proofglyph "*>:" = None.
Proof. reflexivity. Qed.

Example excess_assumption_stack_rejected : decode_proofglyph "**:" = None.
Proof. reflexivity. Qed.

Example excess_proof_stack_rejected : decode_proofglyph "***!" = None.
Proof. reflexivity. Qed.

Example unfinished_stack_rejected : decode_proofglyph "*:*" = None.
Proof. reflexivity. Qed.

Example raw_decode_does_not_check_types : decode_proofglyph "^:" = Some [Assume tKind].
Proof. reflexivity. Qed.

Example checked_decode_rejects_bad_type : check_proofglyph 32 true "^:" = None.
Proof. reflexivity. Qed.

Example compile_identity_to_bytes : compile_proofglyph 32 true identity_source =
  Some ("*:#0#0>#0$0\!", [tType; tPi (tConst 0) (tConst 0)]).
Proof. reflexivity. Qed.

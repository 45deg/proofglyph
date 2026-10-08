From Stdlib Require Import List String.
Import ListNotations.
From Tinyprover.Pa Require Export Syntax CodecImpl CheckerImpl.
From Tinyprover.Tp Require Export CompileImpl.

Definition compile_pa fuel allow src : option (string * list term) :=
  match compile fuel allow src with
  | Some (ds, sg) => Some (encode_pa ds, sg)
  | None => None
  end.

Definition check_pa fuel allow bytes : option (list term) :=
  match decode_pa bytes with
  | Some ds => check_program fuel allow [] ds
  | None => None
  end.


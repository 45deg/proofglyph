open Tinyprover_core
open Term

(** {1 .pg Assembly Reader and Stack Machine}

    Parses symbolic instructions in the .pg language and executes stack-based operations
    to construct terms and register axioms and theorems in the kernel. *)

(** Raised on syntax errors, stack underflow/overflow, or type errors, with byte position. *)
exception Error of string

(** [run ?allow_axioms kernel source] executes the .pg source code against [kernel].
    The stack top is on the right in conceptual notation (represented by the list head).
    Instructions:
    - Whitespace (spaces, tabs, CR, LF): ignored between tokens.
    - [*]  : Push [Type]
    - [^]  : Push [Kind]
    - [$n] : Push [Var n] (followed by decimal integer)
    - [#n] : Push [Const n] (followed by decimal integer)
    - [>]  : Pop [b], pop [a], push [Pi(a,b)]
    - [\]  : Pop [b], pop [a], push [Lam(a,b)]
    - [@]  : Pop [x], pop [f], push [App(f,x)]
    - [:]  : If stack is exactly [[typ]], register [typ] as an axiom and clear stack
    - [!]  : If stack is exactly [[proof; typ]], verify [proof : typ], register it, and clear stack

    @param allow_axioms whether [:] (assumption) is permitted (defaults to [true]; set to [false]
      when checking proofs after a trusted prelude).
    @raise Error on unknown character, index overflow, stack mismatch, non-empty stack at EOF,
      or kernel verification failure. *)
let run ?(allow_axioms=true) kernel source =
  let stack = ref [] in
  let push t = stack := t :: !stack in
  let error i msg = raise (Error (Printf.sprintf "byte %d: %s" i msg)) in
  let binary i constructor = match !stack with
    | b::a::rest -> stack := constructor (a,b) :: rest
    | _ -> error i "stack underflow"
  in
  let n = String.length source in
  let number i =
    let j = ref (i+1) in
    while !j < n && source.[!j] >= '0' && source.[!j] <= '9' do incr j done;
    if !j = i+1 then error i "expected decimal index";
    let value = try int_of_string (String.sub source (i+1) (!j-i-1))
      with Failure _ -> error i "index is too large" in
    value, !j
  in
  let rec scan i = if i < n then (
    let next = ref (i+1) in
    (try (match source.[i] with
      | ' ' | '\n' | '\r' | '\t' -> ()
      | '*' -> push Type | '^' -> push Kind
      | '$' -> let v,j = number i in push (Var v); next := j
      | '#' -> let v,j = number i in push (Const v); next := j
      | '>' -> binary i (fun (a,b) -> Pi(a,b))
      | '\\' -> binary i (fun (a,b) -> Lam(a,b))
      | '@' -> binary i (fun (a,b) -> App(a,b))
      | ':' ->
          if not allow_axioms then error i "assumptions are disabled";
          (match !stack with
           | [typ] -> ignore (Kernel.assume kernel typ); stack := []
           | _ -> error i "assumption requires exactly one stack item")
      | '!' -> (match !stack with
          | [proof;typ] -> ignore (Kernel.prove kernel typ proof); stack := []
          | _ -> error i "proof registration requires exactly two stack items")
      | c -> error i (Printf.sprintf "unknown instruction %C" c))
    with Kernel.Error msg -> error i msg);
    scan !next)
  in scan 0;
  if !stack <> [] then error n "unfinished stack at end of file"

(* The byte parser and I/O are handwritten and remain in the trusted boundary.
   Type checking is performed exclusively by the Rocq-extracted Checker. *)
open Checker

exception Input_error of string

let error offset message =
  raise (Input_error (Printf.sprintf "byte %d: %s" offset message))

(* Extraction retains unary naturals to avoid trusting overflowing int arithmetic.
   Limit conversion work in this unverified input adapter. *)
let index_limit = 100_000
let fuel_limit = 100_000
let nat_of_int n =
  let rec go n acc = if n = 0 then acc else go (n - 1) (S acc) in
  go n O

let parse source =
  let size = String.length source in
  let stack = ref [] in
  let declarations = ref [] in
  let push t = stack := t :: !stack in
  let binary offset make = match !stack with
    | b :: a :: rest -> stack := make a b :: rest
    | _ -> error offset "stack underflow"
  in
  let number offset =
    let pos = ref (offset + 1) in
    let value = ref 0 in
    while !pos < size && source.[!pos] >= '0' && source.[!pos] <= '9' do
      let digit = Char.code source.[!pos] - Char.code '0' in
      if !value > (index_limit - digit) / 10 then
        error offset "index exceeds rocq4pa resource limit (100000)";
      value := !value * 10 + digit;
      incr pos
    done;
    if !pos = offset + 1 then error offset "expected decimal index";
    nat_of_int !value, !pos
  in
  let rec scan offset =
    if offset < size then begin
      let next = ref (offset + 1) in
      (match source.[offset] with
      | ' ' | '\t' | '\r' | '\n' -> ()
      | '*' -> push TType
      | '^' -> push TKind
      | '$' -> let n, pos = number offset in push (TVar n); next := pos
      | '#' -> let n, pos = number offset in push (TConst n); next := pos
      | '>' -> binary offset (fun a b -> TPi (a, b))
      | '\\' -> binary offset (fun a b -> TLam (a, b))
      | '@' -> binary offset (fun a b -> TApp (a, b))
      | ':' -> (match !stack with
          | [a] -> declarations := Assume a :: !declarations; stack := []
          | _ -> error offset "assumption requires exactly one stack item")
      | '!' -> (match !stack with
          | [proof; a] -> declarations := Prove (a, proof) :: !declarations; stack := []
          | _ -> error offset "proof registration requires exactly two stack items")
      | c -> error offset (Printf.sprintf "unknown instruction %C" c));
      scan !next
    end
  in
  scan 0;
  if !stack <> [] then error size "unfinished stack at end of file";
  List.rev !declarations

let read_file path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let usage () =
  prerr_endline "Usage: rocq4pa check FILE [--prelude FILE] [--no-axioms] [--fuel N]";
  exit 2

let run () =
  if Array.length Sys.argv < 3 || Sys.argv.(1) <> "check" then usage ();
  let source = Sys.argv.(2) in
  let prelude = ref None in
  let allow = ref true in
  let fuel = ref 2048 in
  let rec options i =
    if i < Array.length Sys.argv then match Sys.argv.(i) with
    | "--no-axioms" -> allow := false; options (i + 1)
    | "--prelude" when i + 1 < Array.length Sys.argv ->
        prelude := Some Sys.argv.(i + 1); options (i + 2)
    | "--fuel" when i + 1 < Array.length Sys.argv ->
        (match int_of_string_opt Sys.argv.(i + 1) with
        | Some n when n > 0 && n <= fuel_limit -> fuel := n
        | _ -> prerr_endline "fuel must be in 1..100000"; usage ());
        options (i + 2)
    | _ -> usage ()
  in
  options 3;
  let fuel = nat_of_int !fuel in
  let verify allow sg path =
    let declarations = parse (read_file path) in
    match check_program_direct fuel allow sg declarations with
    | Some result -> result
    | None -> raise (Input_error (path ^ ": rejected (type error, forbidden assumption, or exhausted fuel)"))
  in
  let initial = match !prelude with
    | None -> []
    | Some path -> verify true [] path
  in
  let final = verify (!allow && !prelude = None) initial source in
  Printf.printf "accepted: %d declarations (%d from prelude)\n"
    (List.length final) (List.length initial)

let () =
  try run () with
  | Input_error message | Sys_error message -> prerr_endline message; exit 1
  | Stack_overflow -> prerr_endline "rejected: stack limit exceeded"; exit 1
  | Out_of_memory -> prerr_endline "rejected: memory exhausted"; exit 1

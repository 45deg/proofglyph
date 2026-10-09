(* Byte decoding and type checking use the shared Rocq-extracted implementation.
   I/O and the bounded-index resource guard remain host operations. *)
open Checker

exception Input_error of string

let error offset message =
  raise (Input_error (Printf.sprintf "byte %d: %s" offset message))

(* Extracted naturals use Zarith; these bounds remain CLI resource limits. *)
let index_limit = 100_000
let fuel_limit = 100_000
let nat_of_int n =
  if n < 0 then invalid_arg "negative natural";
  Big_int_Z.big_int_of_int n

let parse source =
  let size = String.length source in
  let rec bound_indices offset =
    if offset < size then
      if source.[offset] = '$' || source.[offset] = '#' then (
        let pos = ref (offset + 1) and value = ref 0 in
        while !pos < size && source.[!pos] >= '0' && source.[!pos] <= '9' do
          let digit = Char.code source.[!pos] - Char.code '0' in
          if !value > (index_limit - digit) / 10 then
            error offset "index exceeds proofglyph resource limit (100000)";
          value := !value * 10 + digit;
          incr pos
        done;
        bound_indices !pos)
      else bound_indices (offset + 1)
  in
  bound_indices 0;
  let bytes = List.init size (String.get source) in
  match decode_proofglyph bytes with
  | Some declarations -> declarations
  | None -> raise (Input_error "invalid proofglyph byte syntax or stack")

let read_file path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let usage () =
  prerr_endline "Usage: proofglyph check FILE [--prelude FILE] [--no-axioms] [--fuel N]";
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
    match check_program fuel allow sg declarations with
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

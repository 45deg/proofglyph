(** {1 Type-Checking Kernel}

    Implements the minimal trusted computing base (TCB) for λΠ-calculus:
    type inference, product formation checks, β-equivalence testing,
    and constant registration for axioms and theorems.
    The kernel state [t] is encapsulated as an abstract type, ensuring that
    only verified declarations are recorded in the signature. *)

(** Raised when type checking fails or the verification budget (fuel) is exhausted. *)
exception Error of string

(** Provenance of a registered constant. *)
type origin =
  | Assumption  (** Axiom or hypothesis (registered by type alone). *)
  | Proven      (** Theorem or definition (registered after verifying its proof term). *)

(** Entry for a registered constant in the signature. *)
type entry = {
  typ : Term.t;     (** Type of the constant (closed term). *)
  origin : origin;  (** Provenance of the constant. *)
}

(** Abstract kernel state holding the signature and remaining verification fuel. *)
type t

(** [create ?fuel ()] initializes a fresh, empty kernel instance.
    @param fuel maximum verification step budget (default: 1,000,000).
    @raise Invalid_argument if [fuel < 1]. *)
val create : ?fuel:int -> unit -> t

(** [entries k] returns all constants registered in kernel [k] in registration order. *)
val entries : t -> entry list

(** [infer k term] infers the type of [term] in the empty context.
    @raise Error if [term] is ill-typed or verification fuel is exhausted. *)
val infer : t -> Term.t -> Term.t

(** [assume k typ] verifies that [typ] is well-formed (has sort [Type] or [Kind]
    in the empty context) and registers it as a new opaque axiom.
    Returns the newly assigned constant index (0-indexed).
    @raise Error if [typ] is ill-formed or fuel is exhausted. *)
val assume : t -> Term.t -> int

(** [prove k typ term] verifies that [typ] is well-formed in the empty context,
    checks that [term] has a type β-equivalent to [typ], and registers the constant.
    The proof term itself is discarded from the kernel signature upon successful verification.
    Returns the newly assigned constant index (0-indexed).
    @raise Error if type check fails, proof type mismatches, or fuel is exhausted. *)
val prove : t -> Term.t -> Term.t -> int

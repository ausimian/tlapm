(* Compute substitutivity information. *)
open Property

open E_t


type substitutive_args = bool array


val substitutive_arg: substitutive_args pfuncs
val has_substitutive: 'a Property.wrapped -> bool
val get_substitutive: 'a Property.wrapped -> substitutive_args
val get_substitutive_arg: 'a Property.wrapped -> int -> bool

val compute_subst: ctx -> expr -> expr

(** Whether the application of the defined operator [op] to [args] is
substitutive in the argument at array position [k] (counted from the last
argument): [op] must be substitutive in that position, and the operators
passed for the operator parameters that the position flows through must be
Leibniz, that is, substitutive in all of their own arguments. *)
val substitutive_in: ctx -> defn -> expr list -> int -> bool

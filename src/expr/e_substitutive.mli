(* Compute substitutivity information. *)
open Property

open E_t


type substitutive_args = bool array


val substitutive_arg: substitutive_args pfuncs
val has_substitutive: 'a Property.wrapped -> bool
val get_substitutive: 'a Property.wrapped -> substitutive_args
val get_substitutive_arg: 'a Property.wrapped -> int -> bool

val compute_subst: ctx -> expr -> expr

(** Whether every operator argument of an application of the defined operator
[op] to [args] is substitutive in all of its own arguments. The
substitutivity array of [op] describes its applications only when this
holds. With [formals_leibniz] (default [false]), operator parameters of an
enclosing definition count as Leibniz. *)
val operator_args_leibniz:
    ?formals_leibniz:bool -> ctx -> defn -> expr list -> bool

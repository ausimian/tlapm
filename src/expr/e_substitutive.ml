(* Compute substitutivity information. *)
open Ext
open Property

open E_t


type substitutive_args = bool array

let substitutive_arg: substitutive_args pfuncs =
    Property.make "Expr.Substitutive.substitutive_arg"
let has_substitutive x = Property.has x substitutive_arg
let get_substitutive x = Property.get x substitutive_arg
let get_substitutive_arg x n =
    assert (has_substitutive x);
    let arr = get_substitutive x in
    Array.get arr n


(* The operator parameters that an argument of a definition flows through.
   An argument position of a definition is substitutive only if the operators
   passed for these are Leibniz (substitutive in all of their own arguments):
   `Keep(F(_), a) == F(0) /\ a = 1` is substitutive in `a` whatever `F` is,
   but `Ap(F(_), a) == F(a)` is substitutive in `a` only for a Leibniz `F`.
   A dependency is either on an operator parameter of the definition itself,
   given by its position in the substitutivity array, or on an operator
   parameter of an enclosing definition, as for a `LAMBDA` passed on inside
   it, given by its position in the context counted from the bottom. *)
type leibniz_dep =
    | Param of int
    | Outer of int

let leibniz_deps: leibniz_dep list array pfuncs =
    Property.make "Expr.Substitutive.leibniz_deps"


let make_lambda_hyps params =
    let hyps = List.map
        (fun (v, shp) ->
            Fresh (v, shp, Unknown, Unbounded) @@ v)
        params in
    hyps


(* The position of `Ix n` in `cx`, counted from the bottom. *)
let position cx n = Deque.size cx - n


(* Set to `required_leibniz` below, which needs this class. *)
let required_leibniz_ref :
        (formals_leibniz:bool -> ctx -> defn -> expr list -> int
            -> int list option) ref =
    ref (fun ~formals_leibniz:_ _ _ _ _ -> None)


(* The state of the traversal that computes the substitutivity of one
   parameter: the de Bruijn index of the parameter, whether the current
   subexpression is in substitutive scope, the operator parameters (as
   context positions) that the current subexpression flows through, whether
   every occurrence so far is in substitutive scope, and the operator
   parameters that the occurrences so far flow through. *)
type state = {
    index: int;
    scope: bool;
    through: int list;
    subst: bool ref;
    deps: int list ref;
}


class compute_substitutivity_array = object (self: 'self)
    inherit [state] E_visit.iter as super

    method compute cx e =
        match e.core with
            | Lambda (params, expr) ->
                let hyps = make_lambda_hyps params in
                let n = List.length params in
                let outer = Deque.size cx in
                let cx = Deque.append_list cx hyps in
                let f i =
                    let st = {index = i + 1; scope = true; through = [];
                              subst = ref true; deps = ref []} in
                    self#expr (st, cx) expr;
                    let to_dep p =
                        if p >= outer then Param (Deque.size cx - 1 - p)
                        else Outer p in
                    (!(st.subst), List.map to_dep (Stdlib.List.sort_uniq compare !(st.deps)))
                in
                assert (n > 0);
                let res = Array.init n f in
                (Array.map fst res, Array.map snd res)
            | _ ->
                (Array.make 0 true, Array.make 0 [])

    method expr ((st, cx) as scx) e =
        match e.core with
        | Ix n when n = st.index ->
            if st.scope then st.deps := st.through @ !(st.deps)
            else st.subst := false
        | Lambda (params, expr) ->
            let hyps = make_lambda_hyps params in
            let cx = Deque.append_list cx hyps in
            let st = {st with index = st.index + List.length params} in
            self#expr (st, cx) expr
        | Apply ({core=Internal (Builtin.Prime | StrongPrime
                | Box _ | Diamond | ENABLED | UNCHANGED)},
                [expr]) ->
            self#expr ({st with scope = false}, cx) expr
        | Sub (_, e1, e2)
        | Tsub (_, e1, e2)
        | Fair (_, e1, e2)
        | Apply ({core=Internal (Builtin.Leadsto | Actplus | Cdot)},
                [e1; e2]) ->
            let st = {st with scope = false} in
            self#expr (st, cx) e1;
            self#expr (st, cx) e2
        | Apply ({core = Lambda (params, _)} as op, args)
                when List.length params = List.length args ->
            (* a LAMBDA applied directly, as in `(LAMBDA y : F(y))(a)`:
            the arguments flow wherever the body takes the formals *)
            self#expr scx (E_subst.normalize ~cx op args @@ e)
        | Apply ({core=Ix n} as op_ix, args) ->
            let hyp = E_t.get_val_from_id cx n in
            begin match hyp.core with
            | Defn ({core = Operator _} as op, _, _, _) ->
                (* An argument is in substitutive scope only if the
                enclosing scope is, the operator is substitutive in that
                position, and the operators passed for the parameters that
                the position flows through are Leibniz. Those operators may
                be Leibniz only if operator parameters around them are, so
                the argument flows through these as well. The array is
                indexed from the last parameter, as in `indexed_args`. *)
                let n_args = List.length args in
                List.iteri
                    (fun i arg ->
                        let k = n_args - 1 - i in
                        let st =
                            match !required_leibniz_ref
                                    ~formals_leibniz:true cx op args k with
                            | Some through when get_substitutive_arg op k ->
                                {st with through = through @ st.through}
                            | _ -> {st with scope = false}
                        in
                        self#expr (st, cx) arg)
                    args
            | Fresh (_, Shape_op _, Unknown, _) ->
                (* an operator parameter of this or an enclosing definition,
                which keeps its arguments in substitutive scope if the
                operator passed for it is Leibniz; the same holds for the
                parameter itself, as an application of it compares the
                operators passed for it *)
                let st = {st with through = position cx n :: st.through} in
                self#expr (st, cx) op_ix;
                List.iter (fun arg -> self#expr (st, cx) arg) args
            | Fresh (_, Shape_op _, (State | Action | Temporal), _) ->
                (* A declared operator of non-constant level may prime its
                arguments or apply ENABLED or a temporal operator to them,
                so they are not in substitutive scope. *)
                let st = {st with scope = false} in
                List.iter (fun arg -> self#expr (st, cx) arg) args
            | _ -> super#expr scx e
            end
        | Tquant (_, ls, _) ->
            let st = {st with index = st.index + List.length ls} in
            super#expr (st, cx) e
        | Choose (v, optdom, expr) ->
            let bound = match optdom with
                | None -> Unbounded
                | Some dom ->
                    self#expr scx dom ;
                    Bounded (dom, Visible)
                in
            let hyp = Fresh (v, Shape_expr, Constant, bound) @@ v in
            let cx = Deque.snoc cx hyp in
            self#expr ({st with index = st.index + 1}, cx) expr
        | SetSt (v, dom, expr) ->
            self#expr scx dom;
            let bound = Bounded (dom, Visible) in
            let hyp = Fresh (v, Shape_expr, Constant, bound) @@ v in
            let cx = Deque.snoc cx hyp in
            self#expr ({st with index = st.index + 1}, cx) expr
        | _ -> super#expr scx e

    method defn scx df =
        let (st, cx) = super#defn scx df in
        ({st with index = st.index + 1}, cx)

    method bounds scx bs =
        let (st, cx) = super#bounds scx bs in
        ({st with index = st.index + List.length bs}, cx)

    method instance scx inst =
        assert false  (* `INSTANCE` statements have been expanded *)

    method bound scx b =
        assert false  (* unused method *)

    method hyp scx h =
        assert false  (* sequents do not occur in expressions *)

    method hyps scx hs =
        assert false  (* sequents do not occur in expressions *)
end


let make_arrays cx e =
    let visitor = new compute_substitutivity_array in
    visitor#compute cx e


let all_true arr = Array.for_all (fun b -> b) arr


(* The operator parameters, as context positions, that an operator passed
   as an argument must be Leibniz for it to be Leibniz, or `None` if it may
   not be Leibniz. *)
let outer_deps deps =
    let outer = Stdlib.List.concat_map
        (List.map (function Outer p -> Some p | Param _ -> None))
        (Array.to_list deps) in
    if List.mem None outer then None
    else Some (Stdlib.List.sort_uniq compare (Stdlib.List.filter_map Fun.id outer))


let leibniz_operator ~formals_leibniz cx arg =
    (* Whether `arg`, passed as an operator argument, is substitutive in all
    of its own arguments: `Some ps` if it is when the operator parameters at
    the context positions `ps` are, and `None` if it may not be. A `LAMBDA`
    is if no formal occurs under a prime or a modal operator; a defined
    operator is if it has no operator parameters and its substitutivity
    array says so; a declared operator is if it is `CONSTANT`; an operator
    parameter is if the operator passed for it is; a built-in operator is
    unless it is a prime, `ENABLED`, `UNCHANGED`, `\cdot` or a temporal
    operator. Anything else is treated as not Leibniz. Without
    `formals_leibniz`, nothing that depends on operator parameters is.
    *)
    let conditional ps =
        if ps = [] || formals_leibniz then Some ps else None in
    match arg.core with
    | Lambda _ ->
        let (arr, deps) = make_arrays cx arg in
        if all_true arr then Stdlib.Option.bind (outer_deps deps) conditional
        else None
    | Internal (Builtin.Prime | StrongPrime | ENABLED | Cdot | UNCHANGED
            | Box _ | Diamond | Leadsto | Actplus) -> None
    | Internal _ -> Some []
    | Ix n -> begin
        match (E_t.get_val_from_id cx n).core with
        | Fresh (_, Shape_op _, Constant, _) -> Some []
        | Fresh (_, Shape_op _, Unknown, _) -> conditional [position cx n]
        | Defn ({core = Operator (_, body)} as op, _, _, _) ->
            (* the array of a definition with operator parameters assumes
               that its own operator arguments are Leibniz, which nothing
               checks where it is passed on as an operator argument *)
            let higher_order = match body.core with
              | Lambda (params, _) ->
                  List.exists
                    (fun (_, shp) -> match shp with
                      | Shape_op _ -> true
                      | Shape_expr -> false)
                    params
              | _ -> false
            in
            if higher_order || not (has_substitutive op)
                    || not (all_true (get_substitutive op)) then None
            else if not (Property.has op leibniz_deps) then Some []
            else Stdlib.Option.bind
                (outer_deps (Property.get op leibniz_deps)) conditional
        | _ -> None
        end
    | _ -> None


let required_leibniz ~formals_leibniz cx op args k =
    (* For the application of the defined operator `op` to `args`, the
    operator parameters, as context positions, that must be Leibniz for the
    argument at array position `k` to be substitutive, given the
    substitutivity array of `op`; `None` if it may not be substitutive.
    Without dependency information, the position is taken to flow through
    every operator parameter of `op`.
    *)
    match op.core with
    | Operator (_, {core = Lambda (params, _)})
            when List.length params = List.length args ->
        let n = List.length args in
        let deps =
            if Property.has op leibniz_deps then
                (Property.get op leibniz_deps).(k)
            else
                List.concat (List.mapi
                    (fun i (_, shp) -> match shp with
                        | Shape_op _ -> [Param (n - 1 - i)]
                        | Shape_expr -> [])
                    params)
        in
        let need = function
            | Param m ->
                leibniz_operator ~formals_leibniz cx (List.nth args (n - 1 - m))
            | Outer p ->
                if formals_leibniz && p < Deque.size cx then Some [p] else None
        in
        List.fold_left
            (fun acc dep -> match acc, need dep with
                | Some ps, Some qs -> Some (qs @ ps)
                | _ -> None)
            (Some []) deps
    | _ -> Some []

let () = required_leibniz_ref :=
    fun ~formals_leibniz -> required_leibniz ~formals_leibniz


let substitutive_in cx op args k =
    get_substitutive_arg op k
    && Stdlib.Option.is_some (required_leibniz ~formals_leibniz:false cx op args k)


let shape_to_arity shp =
    match shp with
    | Shape_expr -> assert false
    | Shape_op n -> assert (n >= 1); n


class substitutive_op_visitor = object (self: 'self)
    inherit [unit] E_visit.map_visible_hyp as super

    method expr ((s, cx) as scx) e =
        if has_substitutive e then
            e
        else begin
        match e.core with
        | Apply ({core=Internal
                (Mem | Notmem | Subseteq | Setminus | Cap | Cup)} as op,
                args) ->
            let n = List.length args in
            assert (n = 2);
            let args = List.map (self#expr scx) args in
            let expr = Apply (op, args) @@ e in
            let e_ = E_levels.compute_level cx e in
            let level = E_levels.get_level e_ in
            let ar = if level = 0 then
                    Array.make n true
                else
                    Array.make n false in
            assign expr substitutive_arg ar
        | Apply ({core=Internal
                (Prime | StrongPrime | ENABLED | Cdot | UNCHANGED
                    | Box _ | Diamond | Leadsto | Actplus)} as op, args) ->
            let n = List.length args in
            assert (n >= 1);
            let args = List.map (self#expr scx) args in
            let expr = Apply (op, args) @@ e in
            let ar = Array.make n false in
            assign expr substitutive_arg ar
        | Sub (modal_op, action, subscript) ->
            let action = self#expr scx action in
            let subscript = self#expr scx subscript in
            let expr = Sub (modal_op, action, subscript) @@ e in
            let ar = Array.make 2 false in
            assign expr substitutive_arg ar
        | Apply ({core=Ix n} as op_index, args) ->
            let n_args = List.length args in
            assert (n_args > 0);
            let hyp = E_t.get_val_from_id cx n in
            begin match hyp.core with
            | Fresh (name, shp, kind, _) ->
                begin
                let arity = shape_to_arity shp in
                assert (arity = n_args);
                let is_constant_op = match kind with
                    | Constant -> true
                    | _ -> false in
                let args = List.map (self#expr scx) args in
                let ar = Array.make n_args is_constant_op in
                let op = assign op_index substitutive_arg ar in
                let expr = Apply (op, args) @@ e in
                let ar = Array.make n_args is_constant_op in
                assign expr substitutive_arg ar
                end
            | Defn ({core=Operator (_, expr)}, _, _, _) ->
                begin match expr.core with
                | Lambda (params, _) ->
                    let args = List.map (self#expr scx) args in
                    let is_subst = not (List.exists
                        (fun (_, shp) -> match shp with
                            | Shape_op _ -> true
                            | _ -> false)
                        params) in
                    let ar = Array.make n_args is_subst in
                    let op = assign op_index substitutive_arg ar in
                    let expr = Apply (op, args) @@ e in
                    let ar = Array.make n_args is_subst in
                    assign expr substitutive_arg ar
                | _ ->
                    let e = super#expr scx e in
                    let ar = Array.make n_args true in
                    assign e substitutive_arg ar
                end
            | _ ->
                (* TODO: logic in support of this pattern case *)
                let args = List.map (self#expr scx) args in
                let ar = Array.make n_args true in
                let op = assign op_index substitutive_arg ar in
                let expr = Apply (op, args) @@ e in
                let ar = Array.make n_args true in
                assign expr substitutive_arg ar
            end
        | _ -> super#expr scx e
        end

    method hyp scx h =
        if has_substitutive h then
            (scx, h)
        else begin
        match h.core with
        | Defn ({core=Operator (name, expr)} as op, wd, visibility, e) ->
            let expr = self#expr scx expr in
            let (ar, deps) = make_arrays (snd scx) expr in
            let op = Operator (name, expr) @@ op in
            let op = assign op substitutive_arg ar in
            let op = assign op leibniz_deps deps in
            let h = Defn (op, wd, visibility, e) @@ h in
            (E_visit.adj scx h, h)
        | _ -> super#hyp scx h
        end

    method pform scx p =
        if has_substitutive p then p else super#pform scx p

    method defn scx p =
        if has_substitutive p then p else super#defn scx p
end


let compute_subst cx e =
    let visitor = new substitutive_op_visitor in
    visitor#expr ((), cx) e

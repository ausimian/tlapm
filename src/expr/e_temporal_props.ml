(* Functions for checking temporal properties.

Copyright (C) 2013  INRIA and Microsoft Corporation
*)
open Property
open Ext
open E_t
open E_visit

module B = Builtin


(* Whether the value of [e] is the same in every state. [E_constness.is_const]
   misses some constant applications, such as an equality of constants. *)
let rec value_constant e =
  E_constness.is_const e ||
  match e.core with
  | Internal (B.TRUE | B.FALSE) -> true
  | Apply ({core = Internal (B.Eq | B.Neq | B.Neg | B.Conj | B.Disj
                            | B.Implies | B.Equiv)}, args) ->
      List.for_all value_constant args
  | _ -> false


let visitor = object (self : 'self)
  inherit [bool ref * bool] iter as super

  method expr ((closure, is_box), cx as scx) oe =
    if (!closure = false) then ()
    else match oe.core with
    (* constant expressions are closed *)
    (* temporal declarations are closed as well *)
    | _ when (E_constness.is_const oe) -> () (* closed if constant *)
    (* is_const is missing on some constant symbols like equality *)
    | Internal(B.Eq | B.Neq | B.UNCHANGED) -> () (* should be is_const but is not *)
    (* propositions - TRUE/FALSE  *)
    | Internal (B.TRUE | B.FALSE) -> ()
    (* unary closed operators *)
    | Apply ({core = Internal (B.Box _)}, _) when is_box -> ()
    | Apply ({core = Internal B.Diamond}, _) when (not is_box) -> ()
    (* unary operators *)
    | Apply ({core = Internal ((B.Box _) | B.Diamond | B.Prime)}, [e]) -> self#expr scx e
    | Apply ({core = Internal B.Neg}, [e]) -> self#expr ((closure, not is_box),
    cx) e
    (* binary operators *)
    | Apply ({core = Internal ((B.Conj | B.Disj | B.Implies) as tp)}, [e1;e2]) ->
        let closure1 = ref !closure in
        let closure2 = ref !closure in
        let () = match tp with
        | B.Conj | B.Disj -> self#expr ((closure1, is_box), cx) e1; self#expr ((closure2, is_box), cx) e2
        | B.Implies -> self#expr ((closure1, not is_box), cx) e1; self#expr ((closure2, is_box), cx) e2
        | _ -> assert false
        in
        closure := !closure1 && !closure2
    | Apply ({core = Internal B.Equiv}, [e1;e2]) ->
        let closure1 = ref !closure in
        let closure2 = ref !closure in
        let closure3 = ref !closure in
        let closure4 = ref !closure in
        let () = self#expr ((closure1, not is_box), cx) e1; self#expr ((closure2,
        is_box), cx) e2; self#expr ((closure3, is_box), cx) e1; self#expr
        ((closure4, not is_box), cx) e2
        in
        closure := !closure1 && !closure2 && !closure3 && !closure4
    (* quantifiers over rigid variables commute with [] and <> (the Barcan
       formulas), so a quantified formula is closed when its body is and
       its domains are constant *)
    | Quant (_, bs, _) ->
        let constant_domain (_, _, dom) = match dom with
          | Domain d -> E_constness.is_const d
          | No_domain | Ditto -> true
        in
        if List.for_all constant_domain bs then super#expr scx oe
        else closure := false
    (* lists *)
    | List (_, ls) ->
        let cls = ref !closure in
        let f e = let () = self#expr ((cls, is_box), cx) e in
        !cls in
        closure := (List.for_all f ls)
    (* any other application, such as an equality, a set membership or a
       defined operator, need not keep its value over time even when its
       arguments are closed, so it is closed only if its value is constant *)
    | Apply _ ->
        if not (value_constant oe) then closure := false
    (* a sequent is the implication from its hypotheses to its conclusion:
       facts are checked in the opposite polarity, and a declaration is
       closed only if it introduces a constant over a constant domain *)
    | Sequent sq ->
        let rec spin cx hs = match Deque.front hs with
          | None -> self#expr ((closure, is_box), cx) sq.active
          | Some (h, hs) ->
              begin match h.core with
              | Fact (e, _, _) -> self#expr ((closure, not is_box), cx) e
              | Fresh (_, _, Constant, Unbounded) -> ()
              | Fresh (_, _, Constant, Bounded (d, _)) ->
                  if not (E_constness.is_const d) then closure := false
              | Fresh _ | FreshTuply _ | Flex _ -> closure := false
              | Defn _ -> ()
              end;
              if !closure then spin (snd (adj ((closure, is_box), cx) h)) hs
        in
        spin cx sq.context
    (* unexpended temporal operators *)
    | f ->
        closure := false
end

let box_closure cx e =
  let good = ref true in
  visitor#expr ((good,true), cx) e ;
  !good

let diamond_closure cx e =
  let good = ref true in
  visitor#expr ((good,false), cx) e ;
  !good


(* we should generate box-level here using a expr-visitor and replacing
 * facts (with the known cost of duplicating the context for each
 * sequent. The steps are as follows:
   * 1) if it already has a level (i.e. theorem and axioms get a box level
   * without regard to the sequent in the fact) then we do nothing
   * 2) if the fact is a formula, then we apply Leslie’s algorithm to
   * decide its level.
   * 3) if the fact is a sequent, if all (visible) assumptions are
   * box-level, then the fact is box-level.
*)

let compute_time scx e =
  let e =
    let visitor = object (self: 'self)
      inherit E_constness.const_visitor
    end
    in
    visitor#expr ((), scx) e in
  let e = E_tla_norm.expand_unchanged ((),scx) e in
  let e = E_tla_norm.expand_action ((),scx) e in
  let e = E_tla_norm.expand_fairness ((),scx) e in
  let e = E_tla_norm.expand_leadsto ((),scx) e in
  match e.core with
| _ -> match box_closure scx e with
  | true -> Always
  | _ -> Now

let check_time_change ctx tm = match tm with
| Now -> Now
| Always -> Deque.fold_left begin
  fun acc a -> match a.core with
  | Fact(_,_,Now) -> Now
  | _ -> acc
  end Always ctx
| _ -> failwith "error"

(* Tests of module elaboration that parse a module, so they cannot live in
   [M_elab]: the parser depends on it. *)

let%test_module _ = (module struct

  (* Parse [content] as the module [name] in a file of its own, elaborate
     it with every module it needs, and return it elaborated. *)
  let elaborate name content =
    Loader.Global.setup [];
    let hint = Util.locate (name ^ ".tla") Loc.unknown in
    let hint =
      Property.assign hint M_save.module_content_prop (M_save.String content)
    in
    let mule = M_save.parse_file hint in
    let mcx = Util.Coll.Sm.add mule.core.name.core mule M_standard.initctx in
    let mcx = M_save.complete_load mcx in
    let (mcx, mods) = M_dep.schedule mcx in
    let (_, mules) =
      List.fold_left
        (fun (mcx, mules) m ->
          let (mcx, m, _) = M_elab.normalize mcx Deque.empty m in
          (mcx, m :: mules))
        (mcx, []) mods
    in
    List.find (fun m -> m.Property.core.M_t.name.core = name) mules

  (* Whether the theorem [nm] of [mule] is marked as citable. *)
  let marked mule nm =
    let theorem mu = match mu.Property.core with
      | M_t.Theorem (Some h, _, _, _, _, _) -> h.core = nm
      | _ -> false
    in
    Expr.T.is_param_theorem (List.find theorem mule.Property.core.M_t.body)

  (* The theorem [nm] of [mule]: the context and active part of its
     sequent. *)
  let theorem mule nm =
    let find mu = match mu.Property.core with
      | M_t.Theorem (Some h, sq, _, _, _, _) when h.core = nm -> Some sq
      | _ -> None
    in
    List.find_map find mule.Property.core.M_t.body

  (* Whether [e] is a LAMBDA whose body is a sequent with [n] hypotheses
     before the original theorem. *)
  let lambda_hyps e n =
    match e.Property.core with
    | Expr.T.Lambda (_, {core = Expr.T.Sequent sq}) ->
        Deque.size sq.context >= n
    | _ -> false

  (* A theorem stated after an AXIOM of a parametric instance depends on
     the axiom. The axiom becomes a hypothesis inside the theorem's LAMBDA,
     applied to the instance parameters, so the theorem stays marked as
     citable: citing I(1)!T gives ASSUME 1 = 0 PROVE 1 = 0, not 1 = 0. The
     sequent outside the LAMBDA gets no hypothesis: exposing a theorem drops
     the hypotheses counted in [naxs], which would drop the axiom. A
     theorem stated before the axiom does not depend on it. *)
  let%test "axiom-dependent theorem of a parametric instance keeps the axiom" =
    let mule = elaborate "Outer" {|
---- MODULE Outer ----
---- MODULE Ax ----
CONSTANT k
THEOREM Pre == TRUE
AXIOM k = 0
THEOREM T == k = 0
====
I(x) == INSTANCE Ax WITH k <- x
====
|} in
    let t = Option.get (theorem mule "I!T") in
    marked mule "I!Pre" && marked mule "I!T"
    && Deque.null t.Expr.T.context && lambda_hyps t.Expr.T.active 1
end)

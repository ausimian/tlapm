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

  (* A theorem stated after an AXIOM of a parametric instance depends on
     the axiom, which is dropped when the theorem is exposed, so it must
     not be marked as citable: trusting I(1)!T would prove 1 = 0. A
     theorem stated before the axiom does not depend on it and stays
     marked. Citing either fails today with "Expr.Levels: ARITY", so this
     checks the marks themselves. *)
  let%test "axiom-dependent theorem of a parametric instance is not citable" =
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
    marked mule "I!Pre" && not (marked mule "I!T")
end)

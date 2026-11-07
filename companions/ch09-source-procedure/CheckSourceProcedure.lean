import Chapter09SourceProcedure
import Lean.Elab.Command
import Lean.Util.FoldConsts

open Lean Elab Command

private def isProject (n : Name) : Bool :=
  decide ((n.toString.splitOn "Chapter09").length > 1)

private partial def projectClosure (env : Environment) (pending : List Name)
    (seen : NameSet) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then projectClosure env rest seen
    else
      let seen := seen.insert name
      match env.find? name with
      | none => projectClosure env rest seen
      | some info =>
        let refs := info.type.getUsedConstants.toList ++
          match info.value? (allowOpaque := true) with
          | some value => value.getUsedConstants.toList
          | none => []
        projectClosure env (refs.filter isProject ++ rest) seen

run_cmd do
  liftTermElabM do
    let newInfo ← getConstInfo ``Chapter09.SourceProcedure.theorem_9_3_2_from_text
    let sourceInfo ← getConstInfo ``Chapter09.Source.theorem_9_3_2
    unless ← Meta.isDefEq newInfo.type sourceInfo.type do
      throwError "The new theorem does not have the original theorem's complete type"
    logInfo "PASS_EXACT_ORIGINAL_THEOREM_TYPE"
  let env ← getEnv
  let closure := projectClosure env [``Chapter09.SourceProcedure.theorem_9_3_2_from_text] {}
  let forbidden : List Name := [``Chapter09.cover, ``Chapter09.repair,
    ``Chapter09.weighted_repair_bound, ``Chapter09.strict_weighted_repair_bound,
    ``Chapter09.weak_penalty_optimum_repair, ``Chapter09.strict_penalty_optimizer_feasible,
    ``Chapter09.Source.qNonlinear_eq_alpha, ``Chapter09.Source.qNonlinear_eq_alpha_of_weights,
    ``Chapter09.Source.nonlinear_optimizer_strict,
    ``Chapter09.Source.nonlinear_optimizer_strict_of_weights,
    ``Chapter09.Source.theorem_9_3_2]
  for name in forbidden do
    if closure.contains name then
      throwError "Circular or alternative-route dependency: {name}"
  logInfo "PASS_NO_SIMULTANEOUS_REPAIR_OR_OLD_THEOREM_DEPENDENCY"
  for name in closure.toList do
    logInfo m!"SOURCE_PROCEDURE_DEPENDENCY {name}"

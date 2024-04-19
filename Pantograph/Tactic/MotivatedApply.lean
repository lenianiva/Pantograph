import Lean

open Lean

namespace Pantograph.Tactic

def getForallArgsBody: Expr → List Expr × Expr
  | .forallE _ d b _ =>
    let (innerArgs, innerBody) := getForallArgsBody b
    (d :: innerArgs, innerBody)
  | e => ([], e)
def collectMotiveArguments (forallBody: Expr): SSet Nat :=
  match forallBody with
  | .app (.bvar i) _ => SSet.empty.insert i
  | _ => SSet.empty

def motivatedApply: Elab.Tactic.Tactic := λ stx => do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals: List MVarId ← goal.withContext do
    let recursor ← Elab.Term.elabTerm (stx := stx) .none
    let recursorType ← Meta.inferType recursor

    let (forallArgs, forallBody) := getForallArgsBody recursorType
    let motiveIndices := collectMotiveArguments forallBody
    --IO.println s!"{motiveIndices.toList} from {← Meta.ppExpr forallBody}"

    let numArgs ← Meta.getExpectedNumArgs recursorType

    let rec go (i: Nat) (prev: Array Expr): MetaM (Array Expr) := do
      if i ≥ numArgs then
        return prev
      else
        let argType := forallArgs.get! i
        -- If `argType` has motive references, its goal needs to be placed in it
        let argType := argType.instantiateRev prev
        -- Create the goal
        let userName := if motiveIndices.contains (numArgs - i - 1) then `motive else .anonymous
        let argGoal ← Meta.mkFreshExprMVar argType .syntheticOpaque (userName := userName)
        IO.println s!"Creating [{i}] {← Meta.ppExpr argGoal}"
        let prev :=  prev ++ [argGoal]
        go (i + 1) prev
      termination_by numArgs - i
    let newMVars ← go 0 #[]

    -- FIXME: Add an `Eq` target and swap out the motive type

    --let sourceType := forallBody.instantiateRev newMVars
    --unless ← withTheReader Meta.Context (λ ctx => { ctx with config := { ctx.config with } }) $
    --       Meta.isDefEq sourceType (← goal.getType) do
    --  throwError "invalid mapply: The resultant type {← Meta.ppExpr sourceType} cannot be unified with {← Meta.ppExpr $ ← goal.getType}"

    -- Create the main goal for the return type of the recursor
    goal.assign (mkAppN recursor newMVars)

    let nextGoals ← newMVars.toList.map (·.mvarId!) |>.filterM (not <$> ·.isAssigned)
    pure nextGoals
  Elab.Tactic.setGoals nextGoals

end Pantograph.Tactic

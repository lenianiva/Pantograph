import Lean

open Lean

namespace Pantograph.Tactic

def getForallArgsBody: Expr → List Expr × Expr
  | .forallE _ d b _ =>
    let (innerArgs, innerBody) := getForallArgsBody b
    (d :: innerArgs, innerBody)
  | e => ([], e)

def replaceForallBody: Expr → Expr → Expr
  | .forallE param domain body binderInfo, target =>
    let body := replaceForallBody body target
    .forallE param domain body binderInfo
  | _, target => target

structure RecursorWithMotive where
  args: List Expr
  body: Expr

  -- .bvar index for the motive and major from the body
  iMotive: Nat

namespace RecursorWithMotive

protected def nArgs (info: RecursorWithMotive): Nat := info.args.length

protected def getMotiveType (info: RecursorWithMotive): Expr :=
  let level := info.nArgs - info.iMotive - 1
  let a := info.args.get! level
  a

protected def surrogateMotiveType (info: RecursorWithMotive) (mvars: Array Expr) (resultant: Expr): MetaM Expr := do
  let motiveType := Expr.instantiateRev info.getMotiveType mvars
  let resultantType ← Meta.inferType resultant
  return replaceForallBody motiveType resultantType

protected def conduitType (info: RecursorWithMotive) (mvars: Array Expr) (resultant: Expr): MetaM Expr := do
  let motiveCall := Expr.instantiateRev info.body mvars
  Meta.mkEq motiveCall resultant

end RecursorWithMotive

def getRecursorInformation (recursorType: Expr): Option RecursorWithMotive := do
  let (args, body) := getForallArgsBody recursorType
  if ¬ body.isApp then
    .none
  let iMotive ← match body.getAppFn with
    | .bvar iMotive => pure iMotive
    | _ => .none
  return {
    args,
    body,
    iMotive,
  }

def collectMotiveArguments (forallBody: Expr): SSet Nat :=
  match forallBody with
  | .app (.bvar i) _ => SSet.empty.insert i
  | _ => SSet.empty

/-- Applies a symbol of the type `∀ (motive: α → Sort u) (a: α)..., (motive α)` -/
def motivatedApply (mvarId: MVarId) (recursor: Expr) : MetaM (Array Meta.InductionSubgoal) := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.motivatedApply
  let recursorType ← Meta.inferType recursor
  let resultant ← mvarId.getType

  let info ← match getRecursorInformation recursorType with
    | .some info => pure info
    | .none => throwError "Recursor return type does not correspond with the invocation of a motive: {← Meta.ppExpr recursorType}"

  let rec go (i: Nat) (prev: Array Expr): MetaM (Array Expr) := do
    if i ≥ info.nArgs then
      return prev
    else
      let argType := info.args.get! i
      -- If `argType` has motive references, its goal needs to be placed in it
      let argType := argType.instantiateRev prev
      let bvarIndex := info.nArgs - i - 1
      let argGoal ← if bvarIndex = info.iMotive then
          let surrogateMotiveType ← info.surrogateMotiveType prev resultant
          Meta.mkFreshExprMVar surrogateMotiveType .syntheticOpaque (userName := `motive)
        else
          Meta.mkFreshExprMVar argType .syntheticOpaque (userName := .anonymous)
      let prev :=  prev ++ [argGoal]
      go (i + 1) prev
    termination_by info.nArgs - i
  let mut newMVars ← go 0 #[]

  -- Create the conduit type which proves the result of the motive is equal to the goal
  let conduitType ← info.conduitType newMVars resultant
  let goalConduit ← Meta.mkFreshExprMVar conduitType .natural (userName := `conduit)
  mvarId.assign $ ← Meta.mkEqMP goalConduit (mkAppN recursor newMVars)
  newMVars := newMVars ++ [goalConduit]

  return newMVars.map (λ mvar => { mvarId := mvar.mvarId!})

def evalMotivatedApply : Elab.Tactic.Tactic := fun stx => Elab.Tactic.withMainContext do
  let recursor ← Elab.Term.elabTerm (stx := stx) .none
  let nextGoals ← motivatedApply (← Elab.Tactic.getMainGoal) recursor
  Elab.Tactic.setGoals $ nextGoals.toList.map (·.mvarId)

end Pantograph.Tactic

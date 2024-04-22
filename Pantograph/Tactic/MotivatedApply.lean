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

protected def surrogateMotiveType (info: RecursorWithMotive) (resultant: Expr): MetaM Expr := do
  let motiveType := info.getMotiveType
  let resultantType ← Meta.inferType resultant
  return replaceForallBody motiveType resultantType

protected def phantomType (info: RecursorWithMotive) (mvars: Array Expr) (resultant: Expr): MetaM Expr := do
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
def motivatedApply: Elab.Tactic.Tactic := λ stx => do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals: List MVarId ← goal.withContext do
    let recursor ← Elab.Term.elabTerm (stx := stx) .none
    let recursorType ← Meta.inferType recursor

    let resultant ← goal.getType

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
            let surrogateMotiveType ← info.surrogateMotiveType resultant
            Meta.mkFreshExprMVar surrogateMotiveType .syntheticOpaque (userName := `motive)
          else
            Meta.mkFreshExprMVar argType .syntheticOpaque (userName := .anonymous)
        let prev :=  prev ++ [argGoal]
        go (i + 1) prev
      termination_by info.nArgs - i
    let mut newMVars ← go 0 #[]

    goal.assign (mkAppN recursor newMVars)

    let phantomType ← info.phantomType newMVars resultant
    let goalPhantom ← Meta.mkFreshExprMVar phantomType .syntheticOpaque (userName := `phantom)
    newMVars := newMVars ++ [goalPhantom]

    let nextGoals ← newMVars.toList.map (·.mvarId!) |>.filterM (not <$> ·.isAssigned)
    pure nextGoals
  Elab.Tactic.setGoals nextGoals

end Pantograph.Tactic

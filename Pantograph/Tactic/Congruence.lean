import Lean

open Lean

namespace Pantograph.Tactic

def congruenceArg: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let .some (β, _, _) := (← goal.getType).eq? | throwError "Goal is not an Eq"
  let userName := (← goal.getDecl).userName

  let nextGoals ← goal.withContext do
    let u ← Meta.mkFreshLevelMVar
    let α ← Meta.mkFreshExprMVar (.some $ mkSort u)
      .natural (userName := userName ++ `α)
    let f ← Meta.mkFreshExprMVar (.some <| .forallE .anonymous α β .default)
      .synthetic (userName := userName ++ `f)
    let a₁ ← Meta.mkFreshExprMVar (.some α)
      .synthetic (userName := userName ++ `a₁)
    let a₂ ← Meta.mkFreshExprMVar (.some α)
      .synthetic (userName := userName ++ `a₂)
    let h ← Meta.mkFreshExprMVar (.some $ ← Meta.mkEq a₁ a₂)
      .synthetic (userName := userName ++ `h)
    let conduitType ← Meta.mkEq (← Meta.mkEq (.app f a₁) (.app f a₂)) (← goal.getType)
    let conduit ← Meta.mkFreshExprMVar conduitType
      .synthetic (userName := userName ++ `conduit)
    goal.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongrArg f h)
    return [α, a₁, a₂, f,  h, conduit]
  Elab.Tactic.setGoals <| nextGoals.map (·.mvarId!)

def congruenceFun: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let .some (β, _, _) := (← goal.getType).eq? | throwError "Goal is not an Eq"
  let userName := (← goal.getDecl).userName

  let nextGoals ← goal.withContext do
    let u ← Meta.mkFreshLevelMVar
    let α ← Meta.mkFreshExprMVar (.some $ mkSort u)
      .natural (userName := userName ++ `α)
    let fType := .forallE .anonymous α β .default
    let f₁ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := userName ++ `f₁)
    let f₂ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := userName ++ `f₂)
    let a ← Meta.mkFreshExprMVar (.some α)
      .synthetic (userName := userName ++ `a)
    let h ← Meta.mkFreshExprMVar (.some $ ← Meta.mkEq f₁ f₂)
      .synthetic (userName := userName ++ `h)
    let conduitType ← Meta.mkEq (← Meta.mkEq (.app f₁ a) (.app f₂ a)) (← goal.getType)
    let conduit ← Meta.mkFreshExprMVar conduitType
      .synthetic (userName := userName ++ `conduit)
    goal.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongrFun h a)
    return [α, f₁, f₂, h, a, conduit]
  Elab.Tactic.setGoals <| nextGoals.map (·.mvarId!)

def congruence: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let .some (β, _, _) := (← goal.getType).eq? | throwError "Goal is not an Eq"
  let userName := (← goal.getDecl).userName

  let nextGoals ← goal.withContext do
    let u ← Meta.mkFreshLevelMVar
    let α ← Meta.mkFreshExprMVar (.some $ mkSort u)
      .natural (userName := userName ++ `α)
    let fType := .forallE .anonymous α β .default
    let f₁ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := userName ++ `f₁)
    let f₂ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := userName ++ `f₂)
    let a₁ ← Meta.mkFreshExprMVar (.some α)
      .synthetic (userName := userName ++ `a₁)
    let a₂ ← Meta.mkFreshExprMVar (.some α)
      .synthetic (userName := userName ++ `a₂)
    let h₁ ← Meta.mkFreshExprMVar (.some $ ← Meta.mkEq f₁ f₂)
      .synthetic (userName := userName ++ `h₁)
    let h₂ ← Meta.mkFreshExprMVar (.some $ ← Meta.mkEq a₁ a₂)
      .synthetic (userName := userName ++ `h₂)
    let conduitType ← Meta.mkEq (← Meta.mkEq (.app f₁ a₁) (.app f₂ a₂)) (← goal.getType)
    let conduit ← Meta.mkFreshExprMVar conduitType
      .synthetic (userName := userName ++ `conduit)
    goal.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongr h₁ h₂)
    return [α, f₁, f₂, a₁, a₂, h₁, h₂, conduit]
  Elab.Tactic.setGoals <| nextGoals.map (·.mvarId!)

end Pantograph.Tactic

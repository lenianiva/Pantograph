import Lean

open Lean

namespace Pantograph.Tactic

def congruenceArg: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let .some (beta, _, _) := (← goal.getType).eq? | throwError "Goal is not an Eq"
  -- Create the descendant goals

  let nextGoals ← goal.withContext do
    let u ← Meta.mkFreshLevelMVar
    let alpha ← Meta.mkFreshExprMVar (.some $ mkSort u) .natural .anonymous
    let f ← Meta.mkFreshExprMVar (.some <| .forallE .anonymous alpha beta .default)
      .synthetic (userName := goal.name ++ `f)
    let a₁ ← Meta.mkFreshExprMVar (.some alpha)
      .synthetic (userName := goal.name ++ `a₁)
    let a₂ ← Meta.mkFreshExprMVar (.some alpha)
      .synthetic (userName := goal.name ++ `a₂)
    let h ← Meta.mkEq a₁ a₂
    let conduitType ← Meta.mkEq (← Meta.mkEq (.app f a₁) (.app f a₂)) (← goal.getType)
    let conduit ← Meta.mkFreshExprMVar conduitType
      .synthetic (userName := goal.name ++ `conduit)
    goal.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongrArg f h)
    return [alpha, a₁, a₂, f,  h, conduit]
  Elab.Tactic.setGoals <| nextGoals.map (·.mvarId!)

def congruenceFun: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let .some (beta, _, _) := (← goal.getType).eq? | throwError "Goal is not an Eq"
  -- Create the descendant goals

  let nextGoals ← goal.withContext do
    let u ← Meta.mkFreshLevelMVar
    let alpha ← Meta.mkFreshExprMVar (.some $ mkSort u) .natural .anonymous
    let fType := .forallE .anonymous alpha beta .default
    let f₁ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := goal.name ++ `f₁)
    let f₂ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := goal.name ++ `f₂)
    let a ← Meta.mkFreshExprMVar (.some alpha)
      .synthetic (userName := goal.name ++ `a)
    let h ← Meta.mkEq f₁ f₂
    let conduitType ← Meta.mkEq (← Meta.mkEq (.app f₁ a) (.app f₂ a)) (← goal.getType)
    let conduit ← Meta.mkFreshExprMVar conduitType
      .synthetic (userName := goal.name ++ `conduit)
    goal.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongrFun h a)
    return [alpha, f₁, f₂, h, a, conduit]
  Elab.Tactic.setGoals <| nextGoals.map (·.mvarId!)

def congruence: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let .some (beta, _, _) := (← goal.getType).eq? | throwError "Goal is not an Eq"
  -- Create the descendant goals

  let nextGoals ← goal.withContext do
    let u ← Meta.mkFreshLevelMVar
    let alpha ← Meta.mkFreshExprMVar (.some $ mkSort u) .natural .anonymous
    let fType := .forallE .anonymous alpha beta .default
    let f₁ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := goal.name ++ `f₁)
    let f₂ ← Meta.mkFreshExprMVar (.some fType)
      .synthetic (userName := goal.name ++ `f₂)
    let a₁ ← Meta.mkFreshExprMVar (.some alpha)
      .synthetic (userName := goal.name ++ `a₁)
    let a₂ ← Meta.mkFreshExprMVar (.some alpha)
      .synthetic (userName := goal.name ++ `a₂)
    let h₁ ← Meta.mkEq f₁ f₂
    let h₂ ← Meta.mkEq a₁ a₂
    let conduitType ← Meta.mkEq (← Meta.mkEq (.app f₁ a₁) (.app f₂ a₂)) (← goal.getType)
    let conduit ← Meta.mkFreshExprMVar conduitType
      .synthetic (userName := goal.name ++ `conduit)
    goal.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongr h₁ h₂)
    return [alpha, f₁, f₂, a₁, a₂, h₁, h₂, conduit]
  Elab.Tactic.setGoals <| nextGoals.map (·.mvarId!)

end Pantograph.Tactic

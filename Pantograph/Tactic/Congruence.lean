import Lean

open Lean

namespace Pantograph.Tactic

def congruenceArg (mvarId: MVarId): MetaM (List MVarId) := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.congruenceArg
  let target ← mvarId.getType
  let .some (β, _, _) := (← instantiateMVars target).eq? | throwError "Goal is not an Eq"
  let userName := (← mvarId.getDecl).userName

  let u ← Meta.mkFreshLevelMVar
  let α ← Meta.mkFreshExprSyntheticOpaqueMVar (mkSort u)
    (tag := userName ++ `α)
  let f ← Meta.mkFreshExprSyntheticOpaqueMVar (.forallE .anonymous α β .default)
    (tag := userName ++ `f)
  let a₁ ← Meta.mkFreshExprSyntheticOpaqueMVar α
    (tag := userName ++ `a₁)
  let a₂ ← Meta.mkFreshExprSyntheticOpaqueMVar α
    (tag := userName ++ `a₂)
  let h ← Meta.mkFreshExprSyntheticOpaqueMVar (← Meta.mkEq a₁ a₂)
    (tag := userName ++ `h)
  let conduitType ← Meta.mkEq (← Meta.mkEq (.app f a₁) (.app f a₂)) target
  let conduit ← Meta.mkFreshExprSyntheticOpaqueMVar conduitType
    (tag := userName ++ `conduit)
  mvarId.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongrArg f h)
  let result := [α, a₁, a₂, f,  h, conduit]
  return result.map (·.mvarId!)

def evalCongruenceArg: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals ← congruenceArg goal
  Elab.Tactic.replaceMainGoal nextGoals

def congruenceFun (mvarId: MVarId): MetaM (List MVarId) := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.congruenceFun
  let target ← mvarId.getType
  let .some (β, _, _) := (← instantiateMVars target).eq? | throwError "Goal is not an Eq"
  let userName := (← mvarId.getDecl).userName
  let u ← Meta.mkFreshLevelMVar
  let α ← Meta.mkFreshExprSyntheticOpaqueMVar (mkSort u)
    (tag := userName ++ `α)
  let fType := .forallE .anonymous α β .default
  let f₁ ← Meta.mkFreshExprSyntheticOpaqueMVar fType
    (tag := userName ++ `f₁)
  let f₂ ← Meta.mkFreshExprSyntheticOpaqueMVar fType
    (tag := userName ++ `f₂)
  let a ← Meta.mkFreshExprSyntheticOpaqueMVar α
    (tag := userName ++ `a)
  let h ← Meta.mkFreshExprSyntheticOpaqueMVar (← Meta.mkEq f₁ f₂)
    (tag := userName ++ `h)
  let conduitType ← Meta.mkEq (← Meta.mkEq (.app f₁ a) (.app f₂ a)) target
  let conduit ← Meta.mkFreshExprSyntheticOpaqueMVar conduitType
    (tag := userName ++ `conduit)
  mvarId.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongrFun h a)
  let result := [α, f₁, f₂, h, a, conduit]
  return result.map (·.mvarId!)

def evalCongruenceFun: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals ← congruenceFun goal
  Elab.Tactic.replaceMainGoal nextGoals

def congruence (mvarId: MVarId): MetaM (List MVarId) := mvarId.withContext do
  mvarId.checkNotAssigned `Pantograph.Tactic.congruence
  let target ← mvarId.getType
  let .some (β, _, _) := (← instantiateMVars target).eq? | throwError "Goal is not an Eq"
  let userName := (← mvarId.getDecl).userName
  let u ← Meta.mkFreshLevelMVar
  let α ← Meta.mkFreshExprSyntheticOpaqueMVar (mkSort u)
    (tag := userName ++ `α)
  let fType := .forallE .anonymous α β .default
  let f₁ ← Meta.mkFreshExprSyntheticOpaqueMVar fType
    (tag := userName ++ `f₁)
  let f₂ ← Meta.mkFreshExprSyntheticOpaqueMVar fType
    (tag := userName ++ `f₂)
  let a₁ ← Meta.mkFreshExprSyntheticOpaqueMVar α
    (tag := userName ++ `a₁)
  let a₂ ← Meta.mkFreshExprSyntheticOpaqueMVar α
    (tag := userName ++ `a₂)
  let h₁ ← Meta.mkFreshExprSyntheticOpaqueMVar (← Meta.mkEq f₁ f₂)
    (tag := userName ++ `h₁)
  let h₂ ← Meta.mkFreshExprSyntheticOpaqueMVar (← Meta.mkEq a₁ a₂)
    (tag := userName ++ `h₂)
  let conduitType ← Meta.mkEq (← Meta.mkEq (.app f₁ a₁) (.app f₂ a₂)) target
  let conduit ← Meta.mkFreshExprSyntheticOpaqueMVar conduitType
    (tag := userName ++ `conduit)
  mvarId.assign $ ← Meta.mkEqMP conduit (← Meta.mkCongr h₁ h₂)
  let result := [α, f₁, f₂, a₁, a₂, h₁, h₂, conduit]
  return result.map (·.mvarId!)

def evalCongruence: Elab.Tactic.TacticM Unit := do
  let goal ← Elab.Tactic.getMainGoal
  let nextGoals ← congruence goal
  Elab.Tactic.replaceMainGoal nextGoals

end Pantograph.Tactic

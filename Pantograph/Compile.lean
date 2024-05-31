/- Adapted from lean-training-data by semorrison -/
import Pantograph.Protocol
import Pantograph.Compile.Frontend
import Pantograph.Compile.Elab


open Lean

namespace Pantograph.Compile

--def readCompilationUnits (module : Name) : IO Protocol.CompileUnitsResult := do
--  let steps ← processSource module
--  return { units := steps.map (·.src.toString) }
def collectTacticsFromCompilation (steps : List CompilationStep) : IO (List Protocol.InvokedTactic) := do
  let infoTrees := steps.bind (·.trees)
  let tacticInfoTrees := infoTrees.bind λ tree => tree.filter λ
    | info@(.ofTacticInfo _) => info.isOriginal
    | _ => false
  let tactics := tacticInfoTrees.bind collectTactics
  IO.println s!"{steps.length} compilation steps, {infoTrees.length} trees found, {tacticInfoTrees.length} tactic trees, {tactics.length} tactics found"
  tactics.mapM λ invocation => do
    let goalBefore := (Format.joinSep (← invocation.goalState) "\n").pretty
    let goalAfter := (Format.joinSep (← invocation.goalStateAfter) "\n").pretty
    let tactic ← invocation.ctx.runMetaM {} do
      let t ← Lean.PrettyPrinter.ppTactic ⟨invocation.info.stx⟩
      return t.pretty
    return { goalBefore, goalAfter, tactic }


end Pantograph.Compile

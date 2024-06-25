/- Adapted from lean-training-data by semorrison -/
import Pantograph.Protocol
import Pantograph.Compile.Frontend
import Pantograph.Compile.Elab
import Pantograph.Compile.Parse

open Lean

namespace Pantograph.Compile

def collectTacticsFromCompilation (steps : List CompilationStep) : IO (List Protocol.InvokedTactic) := do
  let infoTrees := steps.bind (·.trees)
  let tacticInfoTrees := infoTrees.bind λ tree => tree.filter λ
    | info@(.ofTacticInfo _) => info.isOriginal
    | _ => false
  let tactics := tacticInfoTrees.bind collectTactics
  tactics.mapM λ invocation => do
    let goalBefore := (Format.joinSep (← invocation.goalState) "\n").pretty
    let goalAfter := (Format.joinSep (← invocation.goalStateAfter) "\n").pretty
    let tactic ← invocation.ctx.runMetaM {} do
      let t ← Lean.PrettyPrinter.ppTactic ⟨invocation.info.stx⟩
      return t.pretty
    return { goalBefore, goalAfter, tactic }

end Pantograph.Compile

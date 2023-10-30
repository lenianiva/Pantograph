import Pantograph.Protocol

namespace Pantograph

namespace Protocol
/-- Set internal names to "" -/
def Goal.devolatilize (goal: Goal): Goal :=
  {
    goal with
    name := "",
    vars := goal.vars.map removeInternalAux,
  }
  where removeInternalAux (v: Variable): Variable :=
    {
      v with
      name := ""
    }
end Protocol

end Pantograph

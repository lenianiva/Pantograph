import Lean

abbrev _root_.Std.HashMap := Lean.HashMap
def List.flatten { α } (li : List (List α)) := List.bind li λ x => x
def List.flatMap { α β } (li : List α) (f : α → List β) := List.bind li f
def Array.back! { α } [Inhabited α] (a : Array α) := a.back?.get!

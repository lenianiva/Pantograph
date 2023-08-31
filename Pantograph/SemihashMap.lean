
namespace Pantograph.SemihashMap

structure Imp (β: Type u) where
  data: Array (Option β)

  -- Number of elements currently in use
  size: Nat

  -- Next index that has never been touched
  allocFront: Nat

  -- Deallocated indices
  deallocs: Array Nat

  -- Number of valid entries in `deallocs` array
  lastDealloc: Nat

namespace Imp

structure WF (m: Imp β): Prop where
  capacity: m.data.size = m.deallocs.size
  front_dealloc: ∀ i: Fin m.deallocs.size, (i < m.allocFront) → (m.deallocs.get i) < m.allocFront
  front_data: ∀ i: Fin m.data.size, (i ≥ m.allocFront) → (m.data.get i).isNone

def empty (capacity := 16): Imp β :=
  {
    data := mkArray capacity .none,
    size := 0,
    allocFront := 0,
    deallocs := mkArray capacity 0,
    lastDealloc := 0,
  }

private theorem list_get_replicate (x: α) (i: Fin (List.replicate n x).length):
    List.get (List.replicate n x) i = x := by
  sorry

theorem empty_wf : WF (empty n: Imp β) := by
  unfold empty
  apply WF.mk
  case capacity =>
    conv =>
      lhs
      congr
      simp
    conv =>
      rhs
      congr
      simp
    simp
  case front_dealloc =>
    simp_all
    intro i
    intro a
    contradiction
  case front_data =>
    simp_all
    intro i
    unfold Imp.data at i
    simp at i
    conv =>
      lhs
      unfold Array.get
      unfold mkArray
      simp [List.replicate]
      rewrite [list_get_replicate]

-- FIXME: Merge this with the well-formed versions below so proof and code can
-- mesh seamlessly.
@[inline] def insert (map: Imp β) (v: β): (Imp β × Nat) :=
  match map.lastDealloc with
  | 0 => -- Capacity is full, buffer expansion is required
    if map.size == map.data.size then
      let nextIndex := map.data.size
      let extendCapacity := map.size
      let result: Imp β := {
        data := (map.data.append #[Option.some v]).append (mkArray extendCapacity .none),
        size := map.size + 1,
        allocFront := map.size + 1,
        deallocs := mkArray (map.data.size + 1 + extendCapacity) 0,
        lastDealloc := 0,
      }
      (result, nextIndex)
    else
      let nextIndex := map.size
      let result: Imp β := {
        map
        with
        data := map.data.set ⟨nextIndex, sorry⟩ (Option.some v),
        size := map.size + 1,
        allocFront := map.allocFront + 1,
      }
      (result, nextIndex)
  | (.succ k) => -- Allocation list has space
    let nextIndex := map.deallocs.get! k
    let result: Imp β := {
      map with
      data := map.data.set ⟨nextIndex, sorry⟩ (Option.some v),
      size := map.size + 1,
      lastDealloc := map.lastDealloc - 1
    }
    (result, nextIndex)

@[inline] def remove (map: Imp β) (index: Fin (map.size)): Imp β :=
  have h: index.val < map.data.size := by sorry
  match map.data.get ⟨index.val, h⟩ with
  | .none => map
  | .some _ =>
    {
      map with
      data := map.data.set ⟨index, sorry⟩ .none,
      size := map.size - 1,
      deallocs := map.deallocs.set ⟨map.lastDealloc, sorry⟩ index,
      lastDealloc := map.lastDealloc + 1,
    }

/-- Retrieval is efficient -/
@[inline] def get? (map: Imp β) (index: Fin (map.size)): Option β :=
  have h: index.val < map.data.size := by sorry
  map.data.get ⟨index.val, h⟩
@[inline] def capacity (map: Imp β): Nat := map.data.size

end Imp


/--
This is like a hashmap but you cannot control the keys.
-/
def _root_.Pantograph.SemihashMap β := {m: Imp β // m.WF}

@[inline] def empty (capacity := 16): SemihashMap β :=
  ⟨ Imp.empty capacity, Imp.empty_wf ⟩
@[inline] def insert (map: SemihashMap β) (v: β): (SemihashMap β × Nat) :=
  let ⟨imp, pre⟩ := map
  let ⟨result, id⟩ := imp.insert v
  ( ⟨ result, sorry ⟩, id)
@[inline] def remove (map: SemihashMap β) (index: Nat): SemihashMap β :=
  let ⟨imp, pre⟩ := map
  let result := imp.remove ⟨index, sorry⟩
  ⟨ result, sorry ⟩
@[inline] def get? (map: SemihashMap β) (index: Nat): Option β :=
  let ⟨imp, _⟩ := map
  imp.get? ⟨index, sorry⟩
@[inline] def size (map: SemihashMap β): Nat :=
  let ⟨imp, _⟩ := map
  imp.size

end Pantograph.SemihashMap

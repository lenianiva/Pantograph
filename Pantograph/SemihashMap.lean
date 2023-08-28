
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

@[inline] def remove (map: Imp β) (index: Nat): Imp β :=
  match map.data.getD index .none with
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
@[inline] def get? (map: Imp β) (index: Nat): Option β :=
  map.data.getD index .none
@[inline] def capacity (map: Imp β): Nat := map.data.size

end Imp

def empty (capacity := 16): Imp β :=
  {
    data := mkArray capacity .none,
    size := 0,
    allocFront := 0,
    deallocs := mkArray capacity 0,
    lastDealloc := 0,
  }

/--
This is like a hashmap but you cannot control the keys.
-/
def _root_.Pantograph.SemihashMap β := Imp β

end Pantograph.SemihashMap

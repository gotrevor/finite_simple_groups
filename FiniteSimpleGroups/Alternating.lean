import Mathlib
import FiniteSimpleGroups.Basic

/-!
# Family 2: Alternating groups `A_n` for `n ≥ 5`

The second-easiest family. `A_n` is the group of even permutations of `n`
points. Its simplicity for `n ≥ 5` was Galois's 1830-something insight and is
the reason there's no general quintic formula.

* `A_1 = A_2 = {e}` (trivial — excluded)
* `A_3 ≅ Z/3Z` (cyclic of prime order — already in Family 1)
* `A_4` has the Klein four-group as a normal subgroup (not simple)
* `A_5` onward: simple. `A_5` is the smallest non-abelian simple group (order 60).

Mathlib **has this**: `Mathlib.GroupTheory.SpecificGroups.Alternating` defines
`alternatingGroup` and contains `alternatingGroup.isSimple_of_five_le_card`
(or similar — search the mathlib namespace for the exact name).
-/

namespace FiniteSimpleGroups

/-- **`A_5` is simple.** Mathlib has this as an `instance` directly:
`alternatingGroup.isSimpleGroup_five` in `Mathlib.GroupTheory.SpecificGroups.Alternating`.
This is the smallest non-abelian finite simple group (order 60). -/
example : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance

/-- `A_n` is simple for `n ≥ 5`. **Status in mathlib v4.29.1:** only `n = 5`
is proven (as `alternatingGroup.isSimpleGroup_five`). The general case
remains `sorry` here — proving it requires a normal-subgroup induction
argument that hasn't yet been formalized at this mathlib version. -/
theorem alternatingGroup_isSimple (n : ℕ) (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) := by
  sorry -- Open in mathlib v4.29.1 for n > 5. For n = 5, see the `example` above.

/-- Bundled: `A_5` is a finite simple group. Mathlib provides all three
instances: `Finite`, `Nontrivial (alternatingGroup (Fin (n+3)))`, and
`isSimpleGroup_five`. -/
noncomputable instance alternating_five_isFSG : IsFSG (alternatingGroup (Fin 5)) where
  finite := inferInstance
  nontrivial := inferInstance
  simple := inferInstance

end FiniteSimpleGroups

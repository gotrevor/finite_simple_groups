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

/-- `A_n` is simple for `n ≥ 5`. Mathlib proves this; we cite rather than
re-derive. -/
theorem alternatingGroup_isSimple (n : ℕ) (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) := by
  sorry -- mathlib: `alternatingGroup.isSimple` or
        -- `alternatingGroup.isSimple_of_five_le_card` (verify exact name).

/-- Bundled: `A_n` is a finite simple group for `n ≥ 5`. -/
@[reducible] def alternating_isFSG (n : ℕ) (hn : 5 ≤ n) :
    IsFSG (alternatingGroup (Fin n)) where
  finite := inferInstance
  nontrivial := by
    sorry -- `A_n` is nontrivial iff `n ≥ 4` (since `|A_n| = n!/2`); for `n ≥ 5`
          -- it has order ≥ 60.
  simple := alternatingGroup_isSimple n hn

end FiniteSimpleGroups

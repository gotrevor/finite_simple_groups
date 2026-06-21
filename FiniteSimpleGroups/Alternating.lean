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

## Why general `A_n` simplicity is an `axiom` here (bucket C — pin-lag)

Per the repository's [one rule](../CFSG_MAP.md): **we never re-derive a result that
is already formalized elsewhere.** General `A_n` simplicity (`n ≥ 5`) *is* in
mathlib — Antoine Chambert-Loir shipped it as `alternatingGroup.isSimpleGroup`
in [PR #36524](https://github.com/leanprover-community/mathlib4/pull/36524)
(`Mathlib/GroupTheory/SpecificGroups/Alternating/Simple.lean`, merged 2026-04-28),
via the Iwasawa criterion. It simply post-dates this repo's mathlib pin (v4.29.1),
which only ships the `n = 5` instance `alternatingGroup.isSimpleGroup_five`.

This file therefore records the general case as a single honest `axiom`
(`alternatingGroup_isSimple`), exactly as the Lie-type / sporadic family files do.

**History:** earlier sessions hand-built the full Galois-1832 cycle-decomposition
proof here (a Case 1–4 dispatch bottoming out in 3 `case_*_witness` axioms). That
scaffold compiled but was, by the one rule, re-derivation of a mathlib theorem
(bucket C, not a brick). It was collapsed to this axiom on 2026-05-31; the complete
worked proof is preserved in git history (commit `22aa823` and ancestors) as
teaching material, not shipped in the working tree.

**TODO when this repo's mathlib pin catches up past #36524:** delete the axiom and
replace every use with the upstream one-liner
```lean
  alternatingGroup.isSimpleGroup (n := Fin n) (by simpa using hn)
```
-/

namespace FiniteSimpleGroups

/-- **`A_5` is simple.** Mathlib v4.29.1 has this as an `instance` directly
(`alternatingGroup.isSimpleGroup_five` in
`Mathlib.GroupTheory.SpecificGroups.Alternating`). This is the smallest
non-abelian finite simple group (order 60). -/
example : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance

/-- **`A_n` is simple for `n ≥ 5`** (Galois, 1832).

Discharged at the v4.31 bump (the "delete-on-bump" trigger): mathlib's
`alternatingGroup.isSimpleGroup` (PR #36524, Iwasawa criterion) is now in the pin,
so this is a real machine-checked theorem rather than a cited `axiom`. -/
theorem alternatingGroup_isSimple (n : ℕ) (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn)

/-- Bundled: `A_5` is a finite simple group. Mathlib provides all three
instances: `Finite`, `Nontrivial (alternatingGroup (Fin 5))`, and
`isSimpleGroup_five`. -/
noncomputable instance alternating_five_isFSG : IsFSG (alternatingGroup (Fin 5)) where
  finite := inferInstance
  nontrivial := inferInstance
  simple := inferInstance

end FiniteSimpleGroups

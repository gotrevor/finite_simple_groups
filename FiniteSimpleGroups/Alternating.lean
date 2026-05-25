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

/-- **Key reduction lemma (Galois 1832).** Any non-trivial normal subgroup of
`A_n` (for `n ≥ 5`) contains a 3-cycle.

This is the technical heart of the simplicity proof. The argument case-analyses
on the cycle type of a non-identity element of the normal subgroup and reduces,
via commutators with carefully-chosen elements of `A_n`, to a 3-cycle. The
case-analysis is conceptually standard but tedious; **mathlib does not yet
have this packaged in v4.29.1**.

Once available, `IsThreeCycle.alternating_Subgroup.normalClosure` immediately closes
the simplicity argument. -/
theorem exists_threeCycle_of_normal {n : ℕ} (hn : 5 ≤ n)
    {N : Subgroup (alternatingGroup (Fin n))} (_hN : N.Normal) (_h_ne_bot : N ≠ ⊥) :
    ∃ σ : alternatingGroup (Fin n),
      (σ : Equiv.Perm (Fin n)).IsThreeCycle ∧ σ ∈ N := by
  sorry -- The Galois argument: cycle-type case analysis on a non-identity element of N.

/-- `A_n` is simple for `n ≥ 5`. **Status in mathlib v4.29.1:** only `n = 5`
proven directly (`alternatingGroup.isSimpleGroup_five`); the general case is
listed as a TODO at the top of `Mathlib.GroupTheory.SpecificGroups.Alternating`.

Trevor's [side-quest doc](../../../../personal/claude/knowledge/core/projects/lean-journey/side-quests/finite-simple-groups.md)
notes this is a genuine half-day mathlib PR (90% confidence) once you take the
`exists_threeCycle_of_normal` step seriously.

Given that helper, the simplicity proof is immediate: any non-trivial normal
subgroup contains a 3-cycle (by the helper), so its normal closure contains
all 3-cycles (by `IsThreeCycle.alternating_Subgroup.normalClosure`), which equals the
whole `A_n` (by `closure_three_cycles_eq_alternating'`). -/
theorem alternatingGroup_isSimple (n : ℕ) (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) := by
  haveI : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simpa using (by omega : 3 ≤ n))
  refine { eq_bot_or_eq_top_of_normal := ?_ }
  intro N hN
  by_cases h_bot : N = ⊥
  · exact Or.inl h_bot
  · -- N is nontrivial and normal. By the Galois lemma it contains a 3-cycle.
    right
    obtain ⟨σ, hσ_three, hσ_mem⟩ := exists_threeCycle_of_normal hn hN h_bot
    -- The normal closure of σ is the whole A_n; since σ ∈ N and N is normal,
    -- this forces N = ⊤.
    have h_nc : Subgroup.normalClosure ({σ} : Set (alternatingGroup (Fin n))) ≤ N :=
      Subgroup.normalClosure_le_normal (by simpa using hσ_mem)
    have h_nc_eq : Subgroup.normalClosure ({σ} : Set (alternatingGroup (Fin n))) = ⊤ := by
      have h_eq : (⟨(σ : Equiv.Perm (Fin n)), hσ_three.mem_alternatingGroup⟩
                   : alternatingGroup (Fin n)) = σ := Subtype.coe_eta σ _
      rw [← h_eq]
      exact hσ_three.alternating_normalClosure (by simpa using hn)
    rw [h_nc_eq] at h_nc
    exact le_antisymm le_top h_nc

/-- Bundled: `A_5` is a finite simple group. Mathlib provides all three
instances: `Finite`, `Nontrivial (alternatingGroup (Fin (n+3)))`, and
`isSimpleGroup_five`. -/
noncomputable instance alternating_five_isFSG : IsFSG (alternatingGroup (Fin 5)) where
  finite := inferInstance
  nontrivial := inferInstance
  simple := inferInstance

end FiniteSimpleGroups

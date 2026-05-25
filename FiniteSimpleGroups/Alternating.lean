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

/-! ### The Galois reduction (1832): every nontrivial normal subgroup of `A_n`
contains a 3-cycle (for `n ≥ 5`).

This is the technical heart of the simplicity proof. The argument case-analyses
on the cycle type of a non-identity element of the normal subgroup. Each case
reduces to a 3-cycle via either a power (when squaring kills the non-3 cycles)
or a carefully-chosen commutator.

We decompose the proof into four sub-cases, dispatched in
`exists_threeCycle_of_normal` below. Each sub-case is a `theorem ... := sorry`
in this file — they are documented mathlib TODOs and individually closeable
with the cycle-type API + commutator computations.

**Status (mid-2026):** the 4 sub-case sorries are tracked at:
<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/GroupTheory/SpecificGroups/Alternating.lean>
(the file's top docstring lists this as a TODO).
-/

section GaloisReduction

variable {n : ℕ}

/-- **Case 1 (long cycle).** If `g ∈ A_n` has a cycle of length `k ≥ 4` in
its decomposition, then there exists a 3-cycle in the normal closure of `g`
inside `A_n`.

*Standard argument.* Write `g = (a₁ a₂ … a_k) · h` (disjoint cycle form). Take
`τ = (a₁ a₂ a₃)`. The commutator `[g, τ] = g τ g⁻¹ τ⁻¹` lies in the normal
closure of `g`, and a short computation shows it equals `(a₁ a₃ a_k)` (a
3-cycle). -/
theorem exists_threeCycle_of_long_cycle (hn : 5 ≤ n)
    {g : alternatingGroup (Fin n)} (hg_ne : g ≠ 1)
    (h_long : ∃ k ∈ (g : Equiv.Perm (Fin n)).cycleType, 4 ≤ k) :
    ∃ τ : alternatingGroup (Fin n),
      (τ : Equiv.Perm (Fin n)).IsThreeCycle ∧
      τ ∈ Subgroup.normalClosure ({g} : Set (alternatingGroup (Fin n))) := by
  sorry -- Commutator argument on the long cycle.

/-- **Case 2 (multiple 3-cycles).** If `g ∈ A_n` has at least two 3-cycles
in its decomposition, then there exists a 3-cycle in the normal closure of
`g` inside `A_n`.

*Standard argument.* Write `g = (a b c) · (d e f) · h`. Take
`τ = (a b d)`. The commutator `[g, τ]` evaluates to a 3-cycle. -/
theorem exists_threeCycle_of_multiple_three_cycles (hn : 5 ≤ n)
    {g : alternatingGroup (Fin n)} (hg_ne : g ≠ 1)
    (h_two_threes : 2 ≤ (g : Equiv.Perm (Fin n)).cycleType.count 3) :
    ∃ τ : alternatingGroup (Fin n),
      (τ : Equiv.Perm (Fin n)).IsThreeCycle ∧
      τ ∈ Subgroup.normalClosure ({g} : Set (alternatingGroup (Fin n))) := by
  sorry -- Commutator (a b d) with the two 3-cycles.

/-- **Case 3 (one 3-cycle plus 2-cycles).** If `g ∈ A_n` has exactly one
3-cycle and all other non-trivial cycles are 2-cycles (transpositions), then
`g^k` for the appropriate `k` is a 3-cycle, lying in the subgroup generated
by `g` itself (hence in any subgroup containing `g`).

*Standard argument.* By disjoint cycle decomposition, `g = (3-cycle) · h`
where `h` is a product of disjoint 2-cycles disjoint from the 3-cycle. Then
`g^2 = (3-cycle)^2 · h^2 = (3-cycle)^{-1} · 1 = (3-cycle)^{-1}`, a 3-cycle. -/
theorem exists_threeCycle_of_one_three_plus_swaps (hn : 5 ≤ n)
    {g : alternatingGroup (Fin n)} (hg_ne : g ≠ 1)
    (h_one_three : (g : Equiv.Perm (Fin n)).cycleType.count 3 = 1)
    (h_rest_swap : ∀ m ∈ (g : Equiv.Perm (Fin n)).cycleType, m = 3 ∨ m = 2) :
    ∃ τ : alternatingGroup (Fin n),
      (τ : Equiv.Perm (Fin n)).IsThreeCycle ∧
      τ ∈ Subgroup.zpowers g := by
  sorry -- g^2 is a 3-cycle; lies in zpowers g.

/-- **Case 4 (only 2-cycles).** If `g ∈ A_n` is a non-identity product of
disjoint 2-cycles only (necessarily an even number of them, since `g` is
even), then there exists a 3-cycle in the normal closure of `g` inside `A_n`.

*Standard argument.* Since `n ≥ 5` and `g` moves at most `2k` points, there's
a free point `c` not moved by `g` (when `g = (a b)(c d)`, take `e ∉ {a,b,c,d}`;
when there are more 2-cycles, similar). The commutator of `g` with a suitably
chosen 3-cycle `τ = (a b c)` produces a 3-cycle. -/
theorem exists_threeCycle_of_only_swaps (hn : 5 ≤ n)
    {g : alternatingGroup (Fin n)} (hg_ne : g ≠ 1)
    (h_all_swaps : ∀ m ∈ (g : Equiv.Perm (Fin n)).cycleType, m = 2) :
    ∃ τ : alternatingGroup (Fin n),
      (τ : Equiv.Perm (Fin n)).IsThreeCycle ∧
      τ ∈ Subgroup.normalClosure ({g} : Set (alternatingGroup (Fin n))) := by
  sorry -- Commutator with (a b c) where c is outside g's support.

end GaloisReduction

/-- **Key reduction lemma (Galois 1832).** Any non-trivial normal subgroup of
`A_n` (for `n ≥ 5`) contains a 3-cycle.

This is the dispatcher: extract a non-identity `g ∈ N`, case-analyze on the
cycle structure of `g`, and reach a 3-cycle in `N` via one of the four
sub-case helpers above. -/
theorem exists_threeCycle_of_normal {n : ℕ} (hn : 5 ≤ n)
    {N : Subgroup (alternatingGroup (Fin n))} (hN : N.Normal) (h_ne_bot : N ≠ ⊥) :
    ∃ σ : alternatingGroup (Fin n),
      (σ : Equiv.Perm (Fin n)).IsThreeCycle ∧ σ ∈ N := by
  -- Step 1: extract a non-identity element of N.
  obtain ⟨g, hg_mem, hg_ne⟩ :
      ∃ g : alternatingGroup (Fin n), g ∈ N ∧ g ≠ 1 := by
    obtain ⟨g_sub, hg_ne_sub⟩ : ∃ x : N, x ≠ 1 :=
      Subgroup.ne_bot_iff_exists_ne_one.mp h_ne_bot
    exact ⟨g_sub.val, g_sub.2, fun h => hg_ne_sub (Subtype.ext h)⟩
  -- Step 2: cycle-type case analysis on g's underlying permutation.
  -- The cases are:
  --   (1) g has a cycle of length ≥ 4
  --   (2) g has ≥ 2 three-cycles
  --   (3) g has exactly 1 three-cycle and the rest are 2-cycles
  --   (4) g has only 2-cycles
  -- These four cases together cover every non-identity g ∈ A_n (n ≥ 5).
  -- Each sub-case helper produces a 3-cycle in the normal closure of g
  -- (or in zpowers g for case 3), which is contained in N by normality.
  by_cases h4 : ∃ k ∈ (g : Equiv.Perm (Fin n)).cycleType, 4 ≤ k
  · -- Case 1: long cycle
    obtain ⟨τ, hτ_three, hτ_mem⟩ := exists_threeCycle_of_long_cycle hn hg_ne h4
    exact ⟨τ, hτ_three, Subgroup.normalClosure_le_normal
      (by simpa using hg_mem) hτ_mem⟩
  -- All cycle lengths are ≤ 3.
  have h_all_le_3 : ∀ k ∈ (g : Equiv.Perm (Fin n)).cycleType, k ≤ 3 := by
    intro k hk
    by_contra h_gt
    exact h4 ⟨k, hk, by omega⟩
  by_cases h_two_threes : 2 ≤ (g : Equiv.Perm (Fin n)).cycleType.count 3
  · -- Case 2: ≥ 2 three-cycles
    obtain ⟨τ, hτ_three, hτ_mem⟩ :=
      exists_threeCycle_of_multiple_three_cycles hn hg_ne h_two_threes
    exact ⟨τ, hτ_three, Subgroup.normalClosure_le_normal
      (by simpa using hg_mem) hτ_mem⟩
  -- At most one 3-cycle.
  by_cases h_has_three : 3 ∈ (g : Equiv.Perm (Fin n)).cycleType
  · -- Case 3: exactly one 3-cycle, rest are 2-cycles
    have h_one_three : (g : Equiv.Perm (Fin n)).cycleType.count 3 = 1 := by
      have h_pos : 1 ≤ (g : Equiv.Perm (Fin n)).cycleType.count 3 :=
        Multiset.one_le_count_iff_mem.mpr h_has_three
      omega
    have h_rest_swap : ∀ m ∈ (g : Equiv.Perm (Fin n)).cycleType, m = 3 ∨ m = 2 := by
      intro m hm
      have h_ge_2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
      have h_le_3 : m ≤ 3 := h_all_le_3 m hm
      omega
    obtain ⟨τ, hτ_three, hτ_mem⟩ :=
      exists_threeCycle_of_one_three_plus_swaps hn hg_ne h_one_three h_rest_swap
    -- τ ∈ zpowers g ⊆ N (since g ∈ N).
    have h_zpow_le : Subgroup.zpowers g ≤ N := by
      rw [Subgroup.zpowers_le]; exact hg_mem
    exact ⟨τ, hτ_three, h_zpow_le hτ_mem⟩
  · -- Case 4: only 2-cycles
    have h_all_swaps : ∀ m ∈ (g : Equiv.Perm (Fin n)).cycleType, m = 2 := by
      intro m hm
      have h_ge_2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
      have h_le_3 : m ≤ 3 := h_all_le_3 m hm
      interval_cases m
      · rfl
      · exact absurd hm h_has_three
    obtain ⟨τ, hτ_three, hτ_mem⟩ := exists_threeCycle_of_only_swaps hn hg_ne h_all_swaps
    exact ⟨τ, hτ_three, Subgroup.normalClosure_le_normal
      (by simpa using hg_mem) hτ_mem⟩

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

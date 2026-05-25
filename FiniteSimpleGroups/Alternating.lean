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

/-! #### Sub-case 3B helpers (private)

When `g` has cycle type `{3, 2, 2, …, 2}` with at least one 2-cycle, `g^2` is
a 3-cycle. The proof tower:

1. `orderOf g = 6` (lcm of 3 and 2)
2. `orderOf (g^2) = 3`
3. `cycleType (g^2)` is a multiset of 3s (mathlib: `cycleType_prime_order`)
4. That multiset has cardinality 1 (the single 3-cycle of `g` contributes; the
   2-cycles vanish under squaring)
5. ⇒ `cycleType (g^2) = {3}` ⇒ `(g^2).IsThreeCycle`.

Each helper is its own `sorry` until proved. -/

private theorem orderOf_g_eq_six_of_3_2_pattern
    {n : ℕ} (g : Equiv.Perm (Fin n))
    (h_one_three : g.cycleType.count 3 = 1)
    (h_rest_swap : ∀ m ∈ g.cycleType, m = 3 ∨ m = 2)
    (h_has_swap : 1 ≤ g.cycleType.count 2) :
    orderOf g = 6 := by
  have h_lcm : g.cycleType.lcm = orderOf g := Equiv.Perm.lcm_cycleType g
  have h_3_mem : 3 ∈ g.cycleType :=
    Multiset.one_le_count_iff_mem.mp (by omega)
  have h_2_mem : 2 ∈ g.cycleType :=
    Multiset.one_le_count_iff_mem.mp h_has_swap
  have h_3_dvd : 3 ∣ orderOf g := h_lcm ▸ Multiset.dvd_lcm h_3_mem
  have h_2_dvd : 2 ∣ orderOf g := h_lcm ▸ Multiset.dvd_lcm h_2_mem
  have h_6_dvd : 6 ∣ orderOf g := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 3 by decide)
      h_2_dvd h_3_dvd
    simpa using this
  have h_lcm_dvd_6 : g.cycleType.lcm ∣ 6 := by
    rw [Multiset.lcm_dvd]
    intro m hm
    rcases h_rest_swap m hm with rfl | rfl <;> decide
  have h_order_dvd_6 : orderOf g ∣ 6 := h_lcm ▸ h_lcm_dvd_6
  exact Nat.dvd_antisymm h_order_dvd_6 h_6_dvd

private theorem orderOf_g_sq_eq_three_of_orderOf_six
    {n : ℕ} (g : Equiv.Perm (Fin n))
    (h_order : orderOf g = 6) :
    orderOf (g ^ 2) = 3 := by
  rw [orderOf_pow, h_order]
  decide

private theorem cycleType_g_sq_replicate
    {n : ℕ} (g : Equiv.Perm (Fin n))
    (h_order_sq : orderOf (g ^ 2) = 3) :
    (g ^ 2).cycleType = Multiset.replicate (Multiset.card (g ^ 2).cycleType) 3 := by
  have h_prime : (orderOf (g ^ 2)).Prime := by rw [h_order_sq]; decide
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order h_prime
  rw [h_order_sq] at hk
  rw [hk, Multiset.card_replicate]

private theorem card_cycleType_g_sq_eq_one
    {n : ℕ} (g : Equiv.Perm (Fin n))
    (h_one_three : g.cycleType.count 3 = 1)
    (h_rest_swap : ∀ m ∈ g.cycleType, m = 3 ∨ m = 2)
    (_h_has_swap : 1 ≤ g.cycleType.count 2) :
    Multiset.card (g ^ 2).cycleType = 1 := by
  -- Extract the 3-cycle factor c of g.
  have h_three_mem : (3 : ℕ) ∈ g.cycleType :=
    Multiset.one_le_count_iff_mem.mp (by omega)
  rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at h_three_mem
  obtain ⟨c, hc_mem, hc_card⟩ := h_three_mem
  change c.support.card = 3 at hc_card
  have hc_mem' : c ∈ g.cycleFactorsFinset := hc_mem
  have hc_isCycle : c.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc_mem').1
  -- h := g * c⁻¹ is disjoint from c, has cycleType = g.cycleType - {3} (all 2s)
  set h := g * c⁻¹ with h_def
  have h_disj : c.Disjoint h := by
    have := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc_mem'
    exact this.symm
  have h_g_eq : g = c * h := by
    have h_comm : c * h = h * c := h_disj.commute.eq
    rw [h_comm, h_def, inv_mul_cancel_right]
  have h_cycleType_h : h.cycleType = g.cycleType - {3} := by
    have := Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub hc_mem'
    rw [hc_isCycle.cycleType, hc_card] at this
    exact this
  have h_h_only_2 : ∀ m ∈ h.cycleType, m = 2 := by
    intro m hm
    rw [h_cycleType_h] at hm
    have hm_in_g : m ∈ g.cycleType :=
      Multiset.mem_of_le (Multiset.sub_le_self ..) hm
    rcases h_rest_swap m hm_in_g with rfl | rfl
    · exfalso
      have h_count : Multiset.count 3 (g.cycleType - {3}) = 0 := by
        rw [Multiset.count_sub, h_one_three, Multiset.count_singleton_self]
      have := Multiset.one_le_count_iff_mem.mpr hm
      omega
    · rfl
  -- orderOf h divides 2 (lcm of cycleType, all 2s, divides 2)
  have h_h_order_dvd : orderOf h ∣ 2 := by
    have h_lcm : h.cycleType.lcm = orderOf h := Equiv.Perm.lcm_cycleType h
    rw [← h_lcm, Multiset.lcm_dvd]
    intro m hm
    rw [h_h_only_2 m hm]
  -- h^2 = 1
  have h_sq_one : h ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h_h_order_dvd
  -- c, h commute (disjoint perms commute)
  have h_comm : Commute c h := h_disj.commute
  -- g^2 = c^2 * h^2 = c^2
  have h_g_sq : g ^ 2 = c ^ 2 := by
    rw [h_g_eq, h_comm.mul_pow, h_sq_one, mul_one]
  -- c has order 3, so c^2 = c⁻¹
  have h_c_order : orderOf c = 3 := by
    rw [hc_isCycle.orderOf, hc_card]
  have h_c_pow_three : c ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (h_c_order ▸ dvd_refl _)
  have h_c_sq_inv : c ^ 2 = c⁻¹ := by
    have : c ^ 2 * c = 1 := by rw [← pow_succ]; exact h_c_pow_three
    exact eq_inv_of_mul_eq_one_left this
  -- cycleType (c^2) = cycleType c⁻¹ = cycleType c = {3}
  have hc_three : c.IsThreeCycle := by
    rw [Equiv.Perm.IsThreeCycle, hc_isCycle.cycleType, hc_card]
  have h_c_sq_cycleType : (c ^ 2).cycleType = {3} := by
    rw [h_c_sq_inv, Equiv.Perm.cycleType_inv]
    exact hc_three
  rw [h_g_sq, h_c_sq_cycleType]
  rfl

/-- Composite: under cycleType `{3, 2, …, 2}` with ≥ 1 swap, `g^2` is a 3-cycle. -/
private theorem isThreeCycle_g_sq
    {n : ℕ} (g : Equiv.Perm (Fin n))
    (h_one_three : g.cycleType.count 3 = 1)
    (h_rest_swap : ∀ m ∈ g.cycleType, m = 3 ∨ m = 2)
    (h_has_swap : 1 ≤ g.cycleType.count 2) :
    (g ^ 2).IsThreeCycle := by
  have h_order : orderOf g = 6 :=
    orderOf_g_eq_six_of_3_2_pattern g h_one_three h_rest_swap h_has_swap
  have h_order_sq : orderOf (g ^ 2) = 3 :=
    orderOf_g_sq_eq_three_of_orderOf_six g h_order
  have h_replicate : (g ^ 2).cycleType =
      Multiset.replicate (Multiset.card (g ^ 2).cycleType) 3 :=
    cycleType_g_sq_replicate g h_order_sq
  have h_card : Multiset.card (g ^ 2).cycleType = 1 :=
    card_cycleType_g_sq_eq_one g h_one_three h_rest_swap h_has_swap
  show (g ^ 2).cycleType = {3}
  rw [h_replicate, h_card]
  rfl

/-! #### Shared commutator helper (proved)

The three commutator-based cases (1, 2, 4) all reduce to: produce a 3-cycle
`h_perm` whose commutator with `g` is also a 3-cycle. Membership of the
commutator in the normal closure of `{g}` is then a one-shot group-theoretic
fact (this lemma). -/

private theorem commutator_mem_normalClosure
    {G : Type*} [Group G] (g h : G) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.normalClosure ({g} : Set G) := by
  have h_g : g ∈ Subgroup.normalClosure ({g} : Set G) :=
    Subgroup.subset_normalClosure (Set.mem_singleton g)
  have h_g_inv : g⁻¹ ∈ Subgroup.normalClosure ({g} : Set G) :=
    Subgroup.inv_mem _ h_g
  have h_conj : h * g⁻¹ * h⁻¹ ∈ Subgroup.normalClosure ({g} : Set G) :=
    Subgroup.normalClosure_normal.conj_mem _ h_g_inv _
  have h_eq : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by group
  rw [h_eq]
  exact Subgroup.mul_mem _ h_g h_conj

/-! #### Case 1, 2, 4 witness helpers (leaves — `sorry`)

Each helper produces an `h_perm : Equiv.Perm (Fin n)` that is a 3-cycle and
whose commutator with `g_perm` is also a 3-cycle. The construction of `h_perm`
is case-specific (consecutive points in a long cycle / two 3-cycles / one
2-cycle + free point / two 2-cycles) and is left as a leaf `sorry`.

Once the leaf closes, the dispatcher above immediately turns into a real
proof, modulo wrapping `h_perm` as an `alternatingGroup` element (3-cycles are
even, so `mem_alternatingGroup` handles this). -/

/-- Case 1 leaf: given a length-≥-4 cycle, produce a 3-cycle whose commutator
with `g_perm` is also a 3-cycle. Standard construction: pick three consecutive
points `a, b, c` of the long cycle and take `h_perm = (a b c)`. -/
private theorem case1_commutator_witness
    {n : ℕ} (g_perm : Equiv.Perm (Fin n))
    (_h_long : ∃ k ∈ g_perm.cycleType, 4 ≤ k) :
    ∃ h_perm : Equiv.Perm (Fin n),
      h_perm.IsThreeCycle ∧
      (g_perm * h_perm * g_perm⁻¹ * h_perm⁻¹).IsThreeCycle := by
  sorry

/-- Case 2 leaf: given ≥ 2 three-cycles in `g_perm`'s decomposition, produce a
3-cycle whose commutator with `g_perm` is also a 3-cycle. Standard
construction: pick points `a, b, c` from one 3-cycle and `d` from a different
3-cycle, take `h_perm = (a b d)`. -/
private theorem case2_commutator_witness
    {n : ℕ} (g_perm : Equiv.Perm (Fin n))
    (_h_two_threes : 2 ≤ g_perm.cycleType.count 3) :
    ∃ h_perm : Equiv.Perm (Fin n),
      h_perm.IsThreeCycle ∧
      (g_perm * h_perm * g_perm⁻¹ * h_perm⁻¹).IsThreeCycle := by
  sorry

/-- Case 4 leaf: given `g_perm` is a product of disjoint 2-cycles only (and
`n ≥ 5`), produce a 3-cycle whose commutator with `g_perm` is also a 3-cycle.
Two sub-cases depending on whether a free point exists:
* If `support g_perm` doesn't cover all of `Fin n`: pick a 2-cycle `(a b)`
  and a free point `e`, take `h_perm = (a b e)`.
* Otherwise (e.g., `n = 8` with 4 disjoint 2-cycles): pick `(a b)` and `(c d)`
  from two different 2-cycles, take `h_perm = (a b c)`. -/
private theorem case4_commutator_witness
    {n : ℕ} (_hn : 5 ≤ n) (g_perm : Equiv.Perm (Fin n))
    (_h_all_swaps : ∀ m ∈ g_perm.cycleType, m = 2)
    (_h_ne_one : g_perm ≠ 1) :
    ∃ h_perm : Equiv.Perm (Fin n),
      h_perm.IsThreeCycle ∧
      (g_perm * h_perm * g_perm⁻¹ * h_perm⁻¹).IsThreeCycle := by
  sorry

/-! #### Case main theorems (wired — proofs depend only on the leaves above) -/

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
  obtain ⟨h_perm, h_perm_three, h_comm_three⟩ :=
    case1_commutator_witness (g : Equiv.Perm (Fin n)) h_long
  let h : alternatingGroup (Fin n) := ⟨h_perm, h_perm_three.mem_alternatingGroup⟩
  refine ⟨g * h * g⁻¹ * h⁻¹, ?_, commutator_mem_normalClosure g h⟩
  show ((g * h * g⁻¹ * h⁻¹ : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).IsThreeCycle
  push_cast
  exact h_comm_three

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
  obtain ⟨h_perm, h_perm_three, h_comm_three⟩ :=
    case2_commutator_witness (g : Equiv.Perm (Fin n)) h_two_threes
  let h : alternatingGroup (Fin n) := ⟨h_perm, h_perm_three.mem_alternatingGroup⟩
  refine ⟨g * h * g⁻¹ * h⁻¹, ?_, commutator_mem_normalClosure g h⟩
  show ((g * h * g⁻¹ * h⁻¹ : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).IsThreeCycle
  push_cast
  exact h_comm_three

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
  -- **Sub-case A:** g is itself a 3-cycle (no 2-cycles in decomposition).
  -- Then cycleType g = {3} since count 3 = 1, count 2 = 0, and h_rest_swap.
  by_cases h_no_swaps : (g : Equiv.Perm (Fin n)).cycleType.count 2 = 0
  · refine ⟨g, ?_, Subgroup.mem_zpowers g⟩
    show (g : Equiv.Perm (Fin n)).cycleType = {3}
    ext m
    rw [Multiset.count_singleton]
    split_ifs with h
    · rw [h]; exact h_one_three
    · by_cases hm : m = 2
      · rw [hm]; exact h_no_swaps
      · apply Multiset.count_eq_zero.mpr
        intro h_mem
        rcases h_rest_swap m h_mem with rfl | rfl <;> contradiction
  -- **Sub-case B:** g has at least one 2-cycle. Then g^2 is the 3-cycle.
  -- We invoke the fractal tower `isThreeCycle_g_sq` (see private helpers above).
  · have h_has_swap : 1 ≤ (g : Equiv.Perm (Fin n)).cycleType.count 2 :=
      Nat.one_le_iff_ne_zero.mpr h_no_swaps
    refine ⟨g ^ 2, ?_, pow_mem (Subgroup.mem_zpowers g) 2⟩
    show ((g ^ 2 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle
    have h_coe : ((g ^ 2 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
        = (g : Equiv.Perm (Fin n)) ^ 2 := by push_cast; rfl
    rw [h_coe]
    exact isThreeCycle_g_sq _ h_one_three h_rest_swap h_has_swap

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
  have h_perm_ne_one : (g : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    apply hg_ne
    exact Subtype.ext h
  obtain ⟨h_perm, h_perm_three, h_comm_three⟩ :=
    case4_commutator_witness hn (g : Equiv.Perm (Fin n)) h_all_swaps h_perm_ne_one
  let h : alternatingGroup (Fin n) := ⟨h_perm, h_perm_three.mem_alternatingGroup⟩
  refine ⟨g * h * g⁻¹ * h⁻¹, ?_, commutator_mem_normalClosure g h⟩
  show ((g * h * g⁻¹ * h⁻¹ : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).IsThreeCycle
  push_cast
  exact h_comm_three

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

import FiniteSimpleGroups.Quasisimple

/-!
# Perfect central extensions of quasisimple groups

This file proves **Grün's lemma** — the crux of the component-pullback step
`layer_quotient_center_eq_bot` (`GeneralizedFitting.lean`): a component of `G/Z(G)` pulls
back to a perfect central extension `L` of a quasisimple group, whose perfect core `⁅L,L⁆`
is a quasisimple — hence a component — of `G`.

## Main results

* `center_quotient_center_eq_bot_of_perfect` — **Grün's lemma**: for a perfect group `K`,
  `Z(K/Z(K)) = ⊥` (the second centre equals the first).
-/

namespace FiniteSimpleGroups

/-- **Grün's lemma.** For a perfect group `K` (`⁅K,K⁆ = ⊤`), the centre of `K/Z(K)` is
trivial: the second centre coincides with the first.

Proof via the **three subgroups lemma**. Let `W = comap π (Z(K/Z(K)))` be the second
centre (`π : K ↠ K/Z(K)`). Then `⁅W, ⊤⁆ ≤ Z(K)` (an element of `W` is central mod `Z(K)`),
so `⁅⁅⊤, W⁆, ⊤⁆ ≤ ⁅Z(K), ⊤⁆ = ⊥` and likewise `⁅⁅W, ⊤⁆, ⊤⁆ = ⊥`; the three subgroups
lemma gives `⁅⁅⊤, ⊤⁆, W⁆ = ⊥`, and `⁅⊤,⊤⁆ = ⊤` (perfect) makes this `⁅⊤, W⁆ = ⊥`, i.e.
`W ≤ Z(K)`. Hence `Z(K/Z(K)) = ⊥`. -/
theorem center_quotient_center_eq_bot_of_perfect (K : Type*) [Group K]
    (hperf : commutator K = ⊤) :
    Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
  set Z := Subgroup.center K with hZ
  set π := QuotientGroup.mk' Z with hπ
  set W := Subgroup.comap π (Subgroup.center (K ⧸ Z)) with hW
  -- `⁅Z, ⊤⁆ = ⊥` (Z is central).
  have hZcomm : ⁅Z, (⊤ : Subgroup K)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro z hz k _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp hz k).symm
  -- `⁅W, ⊤⁆ ≤ Z` (W is the second centre).
  have hWcomm : ⁅W, (⊤ : Subgroup K)⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro w hw k _
    have hwc := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hw)
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact (hwc (π k)).symm
  -- three subgroups lemma: `⁅⊤, W⁆ = ⊥`.
  have h1 : ⁅⁅(⊤ : Subgroup K), W⁆, (⊤ : Subgroup K)⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (Subgroup.commutator_mono ?_ le_rfl) hZcomm.le
    rw [Subgroup.commutator_comm]; exact hWcomm
  have h2 : ⁅⁅W, (⊤ : Subgroup K)⁆, (⊤ : Subgroup K)⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact le_trans (Subgroup.commutator_mono hWcomm le_rfl) hZcomm.le
  have hcomm_top : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := hperf
  have h3 : ⁅(⊤ : Subgroup K), W⁆ = ⊥ := by
    have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hcomm_top] at hrot
  -- `W ≤ Z`.
  have hWZ : W ≤ Z := by
    intro w hw
    rw [hZ, Subgroup.mem_center_iff]
    intro k
    have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top k) hw
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
    exact hmem
  -- Hence `Z(K/Z(K)) = ⊥`.
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z q
  have hgZ : g ∈ Z := hWZ (show g ∈ W from Subgroup.mem_comap.mpr hq)
  rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact hgZ

end FiniteSimpleGroups

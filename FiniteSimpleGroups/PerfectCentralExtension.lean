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

open scoped commutatorElement

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

/-- Central factors drop out of a commutator: `⁅k·c, k'·c'⁆ = ⁅k, k'⁆` when `c, c'` are
central. -/
theorem commutatorElement_mul_central {H : Type*} [Group H] (k k' c c' : H)
    (hc : c ∈ Subgroup.center H) (hc' : c' ∈ Subgroup.center H) :
    ⁅k * c, k' * c'⁆ = ⁅k, k'⁆ := by
  have hcl : ∀ x y z : H, z ∈ Subgroup.center H → ⁅x * z, y⁆ = ⁅x, y⁆ := by
    intro x y z hz
    have hcomm : z * y = y * z := (Subgroup.mem_center_iff.mp hz y).symm
    have hzy : z * y * z⁻¹ = y := by rw [hcomm]; group
    rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
    calc x * z * y * (z⁻¹ * x⁻¹) * y⁻¹
        = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [hzy]
  have hcr : ∀ x y z : H, z ∈ Subgroup.center H → ⁅x, y * z⁆ = ⁅x, y⁆ := by
    intro x y z hz
    have hcomm : z * x⁻¹ = x⁻¹ * z := (Subgroup.mem_center_iff.mp hz x⁻¹).symm
    rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
    calc x * (y * z) * x⁻¹ * (z⁻¹ * y⁻¹)
        = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hcomm]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  rw [hcl k (k' * c') c hc, hcr k k' c' hc']

/-- For a central subgroup `C ≤ Z(H)`, the commutator of `K ⊔ C` collapses to that of `K`:
`⁅K ⊔ C, K ⊔ C⁆ = ⁅K, K⁆`. -/
theorem commutator_sup_central_eq {H : Type*} [Group H] (K C : Subgroup H) [C.Normal]
    (hC : C ≤ Subgroup.center H) :
    ⁅K ⊔ C, K ⊔ C⁆ = ⁅K, K⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_left le_sup_left)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at ha hb
  obtain ⟨k, hk, c, hc, rfl⟩ := ha
  obtain ⟨k', hk', c', hc', rfl⟩ := hb
  rw [commutatorElement_mul_central k k' c c' (hC hc) (hC hc')]
  exact Subgroup.commutator_mem_commutator hk hk'

/-- **The simplicity half of "a perfect central extension of a quasisimple group is
quasisimple".** If `K` is finite and perfect, `C ≤ Z(K)` is central, and `(K/C)/Z(K/C)` is
simple, then `K/Z(K)` is simple. Proof (ported from Aristotle job `9f7b6b74`, re-checked in
our kernel): the image of `Z(K)` under `K ↠ K/C` equals `Z(K/C)` — the `⊇` inclusion uses
**Grün's lemma** (`center_quotient_center_eq_bot_of_perfect`) — so the third isomorphism
theorem gives `(K/C)/Z(K/C) ≃* K/Z(K)`, transporting simplicity. -/
theorem perfect_central_ext_quasisimple (K : Type*) [Group K] [Finite K]
    (hperf : commutator K = ⊤) (C : Subgroup K) [C.Normal] (hC : C ≤ Subgroup.center K)
    (hsimple : IsSimpleGroup ((K ⧸ C) ⧸ Subgroup.center (K ⧸ C))) :
    IsSimpleGroup (K ⧸ Subgroup.center K) := by
  have h_iso : (K ⧸ C) ⧸ Subgroup.center (K ⧸ C) ≃* K ⧸ Subgroup.center K := by
    have h_iso : Subgroup.map (QuotientGroup.mk' C) (Subgroup.center K)
        = Subgroup.center (K ⧸ C) := by
      refine le_antisymm ?_ ?_ <;> intro x <;>
        simp_all +decide [Subgroup.mem_center_iff, Subgroup.mem_map]
      · rintro y hy rfl g
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
        simp +decide [← QuotientGroup.mk_mul, hy]
      · intro hx
        obtain ⟨g, hg⟩ : ∃ g : K, (QuotientGroup.mk' C) g = x := QuotientGroup.mk_surjective x
        have hg_center : (QuotientGroup.mk' (Subgroup.center K)) g
            ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
          have hg_center : ∀ k : K,
              (QuotientGroup.mk' (Subgroup.center K)) (g * k * g⁻¹ * k⁻¹) = 1 := by
            intro k
            have h_comm : (QuotientGroup.mk' C) (g * k * g⁻¹ * k⁻¹) = 1 := by
              simp_all +decide [mul_inv_eq_iff_eq_mul]
            erw [QuotientGroup.eq_one_iff] at *; aesop
          simp_all +decide [Subgroup.mem_center_iff, mul_inv_eq_iff_eq_mul]
          rintro ⟨k⟩; exact hg_center k ▸ rfl
        have := center_quotient_center_eq_bot_of_perfect K hperf
        simp_all +decide [Subgroup.eq_bot_iff_forall]
        exact ⟨g, fun k => by rw [Subgroup.mem_center_iff.mp hg_center k], hg⟩
    have := QuotientGroup.quotientQuotientEquivQuotient C (Subgroup.center K) hC
    convert this; all_goals exact h_iso.symm
  exact MulEquiv.isSimpleGroup h_iso.symm

/-- **A finite perfect central extension of a quasisimple group is quasisimple.** If `Q` is
finite and perfect, `D ≤ Z(Q)` is central, and `Q/D` is quasisimple, then `Q` is
quasisimple. (`Q` is perfect by hypothesis; `Q/Z(Q)` is simple by
`perfect_central_ext_quasisimple`.) -/
theorem isQuasisimple_of_perfect_of_central_quotient {Q : Type*} [Group Q] [Finite Q]
    (hperf : commutator Q = ⊤) {D : Subgroup Q} [D.Normal] (hD : D ≤ Subgroup.center Q)
    (hQ : IsQuasisimple (Q ⧸ D)) : IsQuasisimple Q where
  isPerfect := Group.isPerfect_def.mpr hperf
  isSimpleGroup_quotient_center :=
    perfect_central_ext_quasisimple Q hperf D hD hQ.isSimpleGroup_quotient_center

end FiniteSimpleGroups

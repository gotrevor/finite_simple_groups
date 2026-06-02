import FiniteSimpleGroups.LayerNormal
import FiniteSimpleGroups.PerfectCentralExtension

/-!
# The layer under a central quotient

This file discharges the last residual ingredient of Bender's cornerstone: **a central
quotient of a component-free group is component-free** (`layer_quotient_center_eq_bot`).

The key construction: a component `L̄` of `G/Z(G)` pulls back to a subnormal subgroup
`L = comap π L̄` of `G` which is a perfect central extension of the quasisimple `↥L̄`; its
perfect core `⁅L,L⁆` is a subnormal quasisimple subgroup of `G` — a component —
contradicting `layer G = ⊥`.
-/

namespace FiniteSimpleGroups

open scoped commutatorElement

/-- **A finite group `H` with central `C` and quasisimple `H/C` has a quasisimple derived
subgroup.** `K = commutator H` maps onto the perfect `H/C`, so `K ⊔ C = ⊤` and `⁅K,K⁆ = K`
(`commutator_sup_central_eq`), i.e. `↥K` is perfect. The map `↥K ↠ H/C` has central kernel
`C ⊓ K`, so `↥K/(C ⊓ K) ≅ H/C` is quasisimple, and
`isQuasisimple_of_perfect_of_central_quotient` finishes. -/
theorem isQuasisimple_commutator_of_central_quotient {H : Type*} [Group H] [Finite H]
    (C : Subgroup H) [C.Normal] (hC : C ≤ Subgroup.center H) (hQ : IsQuasisimple (H ⧸ C)) :
    IsQuasisimple ↥(commutator H) := by
  have hmapK : (commutator H).map (QuotientGroup.mk' C) = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective C)]
    exact hQ.isPerfect.commutator_eq_top
  have hsup : commutator H ⊔ C = ⊤ := by
    rw [← QuotientGroup.ker_mk' C, ← Subgroup.comap_map_eq, hmapK, Subgroup.comap_top]
  have hKK : ⁅commutator H, commutator H⁆ = commutator H := by
    rw [← commutator_sup_central_eq (commutator H) C hC, hsup, ← commutator_def]
  have hperfK : commutator ↥(commutator H) = ⊤ := by
    apply Subgroup.map_injective (commutator H).subtype_injective
    rw [Subgroup.map_subtype_commutator, hKK, ← MonoidHom.range_eq_map,
      (commutator H).range_subtype]
  -- `D = C ⊓ (commutator H)`, central in `↥(commutator H)`.
  set K := commutator H with hKdef
  set D := C.subgroupOf K with hDdef
  have hDcentral : D ≤ Subgroup.center K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro k
    have hxc : (x : H) ∈ Subgroup.center H := hC (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa using Subgroup.mem_center_iff.mp hxc (k : H))
  -- `↥K / D ≅ H/C`, hence quasisimple.
  have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp K.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmapK
  have hker : ((QuotientGroup.mk' C).comp K.subtype).ker = D := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have e : (K ⧸ D) ≃* (H ⧸ C) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
  haveI : IsQuasisimple (K ⧸ D) := IsQuasisimple.ofMulEquiv e.symm
  exact isQuasisimple_of_perfect_of_central_quotient hperfK hDcentral inferInstance

end FiniteSimpleGroups

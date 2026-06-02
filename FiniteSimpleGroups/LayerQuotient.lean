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

/-- **A central quotient of a component-free group is component-free.** If `layer G = ⊥`
then `layer (G/Z(G)) = ⊥`. A component `L̄` of `G/Z(G)` pulls back to a subnormal subgroup
`L = comap π L̄` of `G` that is a perfect central extension of the quasisimple `↥L̄`; its
perfect core `K = ⁅L,L⁆` (mapped into `G`) is a subnormal quasisimple subgroup — a component
— so `layer G ≠ ⊥`, a contradiction.

This is the lone residual ingredient of Bender's cornerstone, now discharged: combined with
`isSolvable_aux` (`GeneralizedFitting.lean`) it makes `genFittingSubgroup_self_centralizing`
axiom-free down to the standard trio. -/
theorem layer_quotient_center_eq_bot (G : Type*) [Group G] [Finite G]
    (hE : layer G = ⊥) : layer (G ⧸ Subgroup.center G) = ⊥ := by
  set π := QuotientGroup.mk' (Subgroup.center G) with hπ
  rw [layer, sSup_eq_bot]
  intro Lbar hLbar
  -- `hLbar : IsComponent Lbar`. Pull back to `L = comap π Lbar`, subnormal in `G`.
  set L := Subgroup.comap π Lbar with hLdef
  have hLsub : IsSubnormal L ⊤ := IsSubnormal.comap_top π hLbar.1
  haveI hQLbar : IsQuasisimple Lbar := hLbar.2
  -- `↥L ↠ ↥Lbar` induced by `π`, with central kernel `C = Z(G) ⊓ L`.
  have hmem : ∀ y : L, (π.comp L.subtype) y ∈ Lbar := fun y => Subgroup.mem_comap.mp y.2
  set ψ : L →* Lbar := (π.comp L.subtype).codRestrict Lbar hmem with hψ
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨ybar, hybar⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) ybar
    exact ⟨⟨x, Subgroup.mem_comap.mpr hybar⟩, by apply Subtype.ext; rfl⟩
  set C := (Subgroup.center G).subgroupOf L with hCdef
  have hkerψ : ψ.ker = C := by
    ext y
    rw [hCdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hψ, MonoidHom.codRestrict_apply,
      ← Subtype.coe_inj]
    show π (y : G) = 1 ↔ (y : G) ∈ Subgroup.center G
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  haveI : C.Normal := by rw [← hkerψ]; infer_instance
  have hCcentral : C ≤ Subgroup.center L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro k
    have hxc : (x : G) ∈ Subgroup.center G := Subgroup.mem_subgroupOf.mp hx
    exact Subtype.ext (by simpa using Subgroup.mem_center_iff.mp hxc (k : G))
  have eLC : (L ⧸ C) ≃* Lbar :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  haveI : IsQuasisimple (L ⧸ C) := IsQuasisimple.ofMulEquiv eLC.symm
  -- the perfect core `commutator ↥L` is quasisimple; map it into `G` as `KG`.
  have hQK : IsQuasisimple ↥(commutator L) :=
    isQuasisimple_commutator_of_central_quotient C hCcentral inferInstance
  haveI := hQK
  set KG := (commutator L).map L.subtype with hKGdef
  have hKGsub : IsSubnormal KG ⊤ := by
    refine IsSubnormal.of_characteristic_subgroupOf (Subgroup.map_subtype_le _) ?_ hLsub
    rw [hKGdef, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  haveI hQKG : IsQuasisimple ↥KG :=
    IsQuasisimple.ofMulEquiv (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective)
  -- `KG` is a component, so `KG ≤ layer G = ⊥`; but `↥KG` is quasisimple hence nontrivial.
  have hKGbot : KG = ⊥ := le_bot_iff.mp (hE ▸ (IsComponent.le_layer ⟨hKGsub, hQKG⟩))
  exact absurd hKGbot ((Subgroup.nontrivial_iff_ne_bot KG).mp (IsQuasisimple.nontrivial _))

end FiniteSimpleGroups

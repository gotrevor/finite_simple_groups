import FiniteSimpleGroups.Components

/-!
# `E(G)` is normal

The payoff theorem for the layer is **`layer_normal : (layer G).Normal`**:
conjugation by `g` is the automorphism `MulAut.conj g`, which permutes the
components, so it fixes their join `E(G) = sSup {components}`. The two transport
facts it rests on, neither in mathlib, are built here:

* **quasisimple is a `MulEquiv` invariant** (`IsQuasisimple.ofMulEquiv`), via the
  private helper `map_center_eq` (an iso carries the center onto the center — the
  subgroup-image equality `QuotientGroup.congr` needs);
* **subnormality is stable under the `MulAut` action** (`IsSubnormal.smul`), proved
  through the normalizer rephrasing `isNormalStep_iff_le_normalizer` (which dodges
  the `subgroupOf` dependent typing) plus `smul_normalizer`.

These assemble into `isComponent_smul` / `isComponent_smul_iff` (the component set
is conjugation-stable) and finally `layer_normal`. All complete and axiom-clean.
-/

namespace FiniteSimpleGroups

open Subgroup (center)

/-- An isomorphism carries the center onto the center: `(center Q).map e = center Q'`.
mathlib has `Subgroup.centerCongr` (the centers are isomorphic) but not this
subgroup-image equality, which is what `QuotientGroup.congr` needs.

Proved element-wise off mathlib's `MulEquivClass.apply_mem_center` /
`apply_mem_center_iff` (membership in `Set.center` transports across an iso both
ways), which sidesteps any `MulEquiv`/`MonoidHom` coercion juggling. -/
private theorem map_center_eq {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (center Q).map (e : Q →* Q') = center Q' := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using MulEquivClass.apply_mem_center e hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    have hy' : e (e.symm y) ∈ center Q' := by simpa using hy
    exact (MulEquivClass.apply_mem_center_iff e).mp hy'

/-- **Quasisimple is a `MulEquiv` invariant.** If `Q ≃* Q'` and `Q` is quasisimple,
so is `Q'`: perfectness transports by `Group.IsPerfect.ofSurjective` (an iso is
surjective), and the simple central quotient transports by `QuotientGroup.congr`
(carrying `Q ⧸ Z(Q)` to `Q' ⧸ Z(Q')` via `map_center_eq`) plus
`MulEquiv.isSimpleGroup`. -/
theorem IsQuasisimple.ofMulEquiv {Q Q' : Type*} [Group Q] [Group Q']
    [h : IsQuasisimple Q] (e : Q ≃* Q') : IsQuasisimple Q' := by
  refine ⟨?_, ?_⟩
  · -- perfect (complete)
    haveI := h.isPerfect
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · -- simple central quotient: transport `Q ⧸ Z(Q)` simple along the iso
    haveI := h.isSimpleGroup_quotient_center
    exact (QuotientGroup.congr (center Q) (center Q') e (map_center_eq e)).symm.isSimpleGroup

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Pointwise conjugation of a subgroup by `a : MulAut G` is the image under the
underlying equiv `MulDistribMulAction.toMulEquiv G a`. This lets us reuse mathlib's
`≃*`-based subgroup lemmas (`map_equiv_normalizer_eq`, `map_top_of_surjective`). -/
private theorem smul_eq_map (a : MulAut G) (S : Subgroup G) :
    a • S = S.map (MulDistribMulAction.toMulEquiv G a : G →* G) := rfl

/-- The `MulAut` action commutes with `normalizer`: an automorphism sends the
normalizer of `H` to the normalizer of `a • H`. -/
private theorem smul_normalizer (a : MulAut G) (H : Subgroup G) :
    a • Subgroup.normalizer (H : Set G)
      = Subgroup.normalizer ((a • H : Subgroup G) : Set G) := by
  rw [smul_eq_map a (Subgroup.normalizer (H : Set G)), smul_eq_map a H]
  exact Subgroup.map_equiv_normalizer_eq H (MulDistribMulAction.toMulEquiv G a)

/-- `IsNormalStep` rephrased via the normalizer, dodging the `subgroupOf`
dependent typing (`Subgroup.normal_subgroupOf_iff_le_normalizer`). -/
theorem isNormalStep_iff_le_normalizer {H K : Subgroup G} :
    IsNormalStep H K ↔ H ≤ K ∧ K ≤ Subgroup.normalizer H :=
  ⟨fun ⟨hHK, hN⟩ => ⟨hHK, (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN⟩,
    fun ⟨hHK, hn⟩ => ⟨hHK, (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr hn⟩⟩

/-- A normal step transports under the `MulAut` action. -/
theorem IsNormalStep.smul (a : MulAut G) {H K : Subgroup G} (h : IsNormalStep H K) :
    IsNormalStep (a • H) (a • K) := by
  rw [isNormalStep_iff_le_normalizer] at h ⊢
  obtain ⟨hHK, hn⟩ := h
  refine ⟨Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hHK, ?_⟩
  rw [← smul_normalizer]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hn

/-- Subnormality transports under the `MulAut` action: an automorphism sends a
normal chain to a normal chain. -/
theorem IsSubnormal.smul (a : MulAut G) {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (a • H) (a • K) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | tail _ hstep ih => exact ih.tail (hstep.smul a)

/-- **The conjugate of a component is a component.** Subnormality transports by
`IsSubnormal.smul` (with `a • ⊤ = ⊤`); quasisimplicity by `IsQuasisimple.ofMulEquiv`
along `Subgroup.equivSMul a K : ↥K ≃* ↥(a • K)`. -/
theorem isComponent_smul (a : MulAut G) {K : Subgroup G} (h : IsComponent K) :
    IsComponent (a • K) := by
  refine ⟨?_, ?_⟩
  · have hsub := h.isSubnormal.smul a
    rwa [smul_eq_map a (⊤ : Subgroup G),
      Subgroup.map_top_of_surjective (MulDistribMulAction.toMulEquiv G a : G →* G)
        (MulDistribMulAction.toMulEquiv G a).surjective] at hsub
  · haveI := h.isQuasisimple
    exact IsQuasisimple.ofMulEquiv (Subgroup.equivSMul a K)

/-- `IsComponent` is invariant under the `MulAut` action (the inverse automorphism
transports back). -/
theorem isComponent_smul_iff (a : MulAut G) {K : Subgroup G} :
    IsComponent (a • K) ↔ IsComponent K := by
  refine ⟨fun h => ?_, isComponent_smul a⟩
  have := isComponent_smul a⁻¹ h
  rwa [inv_smul_smul] at this

/-- **The layer `E(G)` is normal.** Conjugation by `g` is the automorphism
`MulAut.conj g`, which permutes the components (`isComponent_smul_iff`), hence fixes
the component set and therefore its join `E(G) = sSup {components}`. -/
theorem layer_normal : (layer G).Normal := by
  refine Subgroup.Normal.of_conjugate_fixed (fun g => ?_)
  have hset : (fun K => MulAut.conj g • K) '' {K : Subgroup G | IsComponent K}
      = {K : Subgroup G | IsComponent K} := by
    ext K
    simp only [Set.mem_image, Set.mem_setOf_eq]
    refine ⟨fun ⟨L, hL, hLK⟩ => hLK ▸ isComponent_smul _ hL, fun hK => ?_⟩
    exact ⟨(MulAut.conj g)⁻¹ • K, (isComponent_smul_iff _).mp (by rwa [smul_inv_smul]),
      smul_inv_smul _ _⟩
  rw [layer_eq_sSup, Subgroup.pointwise_smul_def, (Subgroup.gc_map_comap _).l_sSup]
  simp only [← Subgroup.pointwise_smul_def]
  rw [← sSup_image, hset]

/-! ### `E(N) ≤ E(G)` for `N ⊴ G` — the layer pushes forward along `N ↪ G`

The layer analogue of `fittingSubgroup_map_subtype_le`: a component of a normal
subgroup is a component of the whole group, so `E(N)` lands inside `E(G)`. This is
the layer-monotonicity step the induction in Bender's cornerstone
(`genFittingSubgroup_self_centralizing`) needs alongside the Fitting one. -/

variable {N : Subgroup G}

/-- A normal step in `↥N` maps to a normal step in `G` under the inclusion `N ↪ G`:
inclusion is monotone and `(normalizer A).map f ≤ normalizer (A.map f)`
(`Subgroup.le_normalizer_map`). -/
theorem isNormalStep_map_subtype {A B : Subgroup N} (h : IsNormalStep A B) :
    IsNormalStep (A.map N.subtype) (B.map N.subtype) := by
  rw [isNormalStep_iff_le_normalizer] at h ⊢
  exact ⟨Subgroup.map_mono h.1, (Subgroup.map_mono h.2).trans (Subgroup.le_normalizer_map _)⟩

/-- Subnormality in `↥N` maps to subnormality in `G`: lift the chain of normal steps
along the inclusion (`Relation.ReflTransGen.lift`). -/
theorem isSubnormal_map_subtype {A B : Subgroup N} (h : IsSubnormal A B) :
    IsSubnormal (A.map N.subtype) (B.map N.subtype) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | tail _ hstep ih => exact ih.tail (isNormalStep_map_subtype hstep)

/-- **A component of a normal subgroup is a component of the whole group.** If
`N ⊴ G` and `K` is a component of `↥N`, then its image in `G` is a component:
subnormal — the chain `K ◁◁ N` maps in (`isSubnormal_map_subtype`, using
`(⊤ : Subgroup N).map N.subtype = N`) and stacks onto `N ◁ G` — and quasisimple, an
iso-invariant (`IsQuasisimple.ofMulEquiv` along `Subgroup.equivMapOfInjective`). -/
theorem isComponent_map_subtype [N.Normal] {K : Subgroup N} (h : IsComponent K) :
    IsComponent (K.map N.subtype) := by
  have htop : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨?_, ?_⟩
  · have h1 := isSubnormal_map_subtype h.isSubnormal
    rw [htop] at h1
    exact h1.trans (Subgroup.Normal.isSubnormal_top ‹N.Normal›)
  · haveI := h.isQuasisimple
    exact IsQuasisimple.ofMulEquiv (Subgroup.equivMapOfInjective K N.subtype N.subtype_injective)

/-- **`E(N) ≤ E(G)` for a normal subgroup `N ⊴ G`.** Each component of `N` maps to a
component of `G` (`isComponent_map_subtype`), so the join of the former lands inside
the join of the latter. The layer analogue of `fittingSubgroup_map_subtype_le`. -/
theorem layer_map_subtype_le [N.Normal] : (layer N).map N.subtype ≤ layer G := by
  rw [layer_eq_sSup, (Subgroup.gc_map_comap N.subtype).l_sSup]
  exact iSup₂_le fun K hK => (isComponent_map_subtype hK).le_layer

end FiniteSimpleGroups

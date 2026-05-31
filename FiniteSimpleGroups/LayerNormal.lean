import FiniteSimpleGroups.Components

/-!
# `E(G)` is normal — transport lemmas

The payoff theorem for the layer is **`layer_normal : (layer G).Normal`**:
conjugation permutes the components, so their join `E(G)` is conjugation-stable,
hence normal. Reaching it needs two transport facts, neither in mathlib:

* **quasisimple is a `MulEquiv` invariant** (`IsQuasisimple.ofMulEquiv`) — this file;
* **subnormal is stable under conjugation** (next file).

This file provides the quasisimple half (`IsQuasisimple.ofMulEquiv`), built on the
private helper `map_center_eq` (an iso carries the center onto the center, the
subgroup-image equality `QuotientGroup.congr` needs). Both are complete and
axiom-clean.
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

end FiniteSimpleGroups

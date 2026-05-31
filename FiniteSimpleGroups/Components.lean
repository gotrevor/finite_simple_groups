import FiniteSimpleGroups.Quasisimple
import FiniteSimpleGroups.Subnormal

/-!
# Components and the layer `E(G)`

The **layer** `E(G)` is the join of the *components* of `G`, where a **component**
is a **subnormal quasisimple** subgroup (Solomon, Bull. AMS 38, 2001, p. 343).
Together with the Fitting subgroup `F(G)` (`FittingSubgroup.lean`) it forms the
generalized Fitting subgroup `F*(G) = E(G)·F(G)`, on which the whole CFSG
architecture hangs.

This file assembles the two prior bricks:

* `IsQuasisimple` (`Quasisimple.lean`) — perfect with simple central quotient;
* `IsSubnormal` (`Subnormal.lean`) — a finite chain of normal steps.

into the definition of a component and the layer, and proves the structural facts
reachable now. The deeper theorem **`E(G)` is normal** (conjugation permutes the
components) needs two transport lemmas not yet built — `IsQuasisimple` under
`MulEquiv` and `IsSubnormal` under conjugation — and is the next target; see the
module note below.

## Main definitions

* `IsComponent K` — `K` is subnormal in `G` and `↥K` is quasisimple.
* `layer G` (`E(G)`) — the supremum of all components.

## Main results

* `IsComponent.isSubnormal`, `.isQuasisimple` — projections.
* `IsComponent.le_layer` — a component lies in `E(G)`.
* `layer_eq_bot_iff_forall` / structural `sSup` facts.

## Next (needs a stable session)

`layer_normal : (layer G).Normal`. Proof shape: for `g : G`, the pointwise
conjugate `g • K` of a component `K` is again a component, because conjugation is
an automorphism (`MulAut.conj g`):

* quasisimple transports along the `MulEquiv` `↥K ≃* ↥(g • K)` — prove
  `IsQuasisimple.ofMulEquiv` using `Group.IsPerfect.ofSurjective` (image of perfect
  is perfect) + `QuotientGroup.congr` (mathlib, `QuotientGroup/Basic.lean`) carrying
  `↥K ⧸ center` to `↥(g • K) ⧸ center` via `MulEquiv.apply_mem_center_iff`;
* subnormal transports because an automorphism sends a normal chain to a normal
  chain — prove `IsSubnormal.map`/conj on the `IsNormalStep` relation.

Then `sSup` of the component set is conjugation-fixed
(`Subgroup.Normal.of_conjugate_fixed`, as in `FittingSubgroup.sSup_normal_of_forall_normal`).
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

/-- `K` is a **component** of `G`: a subnormal quasisimple subgroup. -/
def IsComponent (K : Subgroup G) : Prop :=
  IsSubnormal K ⊤ ∧ IsQuasisimple K

/-- The **layer** `E(G)`: the join (supremum) of all components of `G`. -/
def layer (G : Type*) [Group G] : Subgroup G :=
  sSup {K : Subgroup G | IsComponent K}

namespace IsComponent

/-- A component is subnormal in `G`. -/
theorem isSubnormal {K : Subgroup G} (h : IsComponent K) : IsSubnormal K ⊤ := h.1

/-- A component is quasisimple. -/
theorem isQuasisimple {K : Subgroup G} (h : IsComponent K) : IsQuasisimple K := h.2

/-- A component lies inside the layer `E(G)`. -/
theorem le_layer {K : Subgroup G} (h : IsComponent K) : K ≤ layer G :=
  le_sSup h

end IsComponent

/-- `E(G)` is the supremum of the components, by definition; rephrased as the
universal property `K ≤ E(G)` for every component, plus minimality. -/
theorem layer_eq_sSup : layer G = sSup {K : Subgroup G | IsComponent K} := rfl

/-- The layer is below any subgroup containing every component. -/
theorem layer_le {H : Subgroup G} (h : ∀ K, IsComponent K → K ≤ H) : layer G ≤ H :=
  sSup_le h

/-- If `G` has no components, its layer is trivial. -/
theorem layer_eq_bot_of_no_components (h : ∀ K : Subgroup G, ¬ IsComponent K) :
    layer G = ⊥ := by
  have hempty : {K : Subgroup G | IsComponent K} = ∅ := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact h K
  rw [layer_eq_sSup, hempty, sSup_empty]

end FiniteSimpleGroups

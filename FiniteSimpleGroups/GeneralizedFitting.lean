import FiniteSimpleGroups.LayerNormal
import FiniteSimpleGroups.FittingSubgroup

/-!
# The generalized Fitting subgroup `F*(G)`

The **generalized Fitting subgroup** `F*(G) = E(G)·F(G)` is the object the whole
CFSG architecture hangs on (Solomon, Bull. AMS 38, 2001, p. 343). It joins the two
bricks built in the prior files:

* the **layer** `E(G)` (`Components.lean`/`LayerNormal.lean`) — the join of the
  components, now known to be normal (`layer_normal`);
* the **Fitting subgroup** `F(G)` (`FittingSubgroup.lean`) — the join of the normal
  nilpotent subgroups, normal and nilpotent (`fittingSubgroup_normal`).

Since `E(G)` and `F(G)` are both normal, `F*(G) = E(G) ⊔ F(G)` is normal too — the
first fact below. The deep property that makes `F*(G)` the cornerstone of the theory
is that it is **self-centralizing**, `C_G(F*(G)) ≤ F*(G)`: in a (suitable) group the
structure is controlled by `F*(G)`. That is the next target; this file establishes
the definition and the normality.

## Main definitions

* `genFittingSubgroup G` (`F*(G)`) — `layer G ⊔ fittingSubgroup G`.

## Main results

* `genFittingSubgroup_normal` — `F*(G)` is normal.
* `layer_le_genFittingSubgroup`, `fittingSubgroup_le_genFittingSubgroup` — both
  factors lie in `F*(G)`.
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

/-- The **generalized Fitting subgroup** `F*(G) = E(G)·F(G)`, realized as the join
`E(G) ⊔ F(G)` of the layer and the Fitting subgroup. -/
def genFittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  layer G ⊔ fittingSubgroup G

/-- The layer `E(G)` lies in `F*(G)`. -/
theorem layer_le_genFittingSubgroup : layer G ≤ genFittingSubgroup G :=
  le_sup_left

/-- The Fitting subgroup `F(G)` lies in `F*(G)`. -/
theorem fittingSubgroup_le_genFittingSubgroup : fittingSubgroup G ≤ genFittingSubgroup G :=
  le_sup_right

/-- **`F*(G)` is normal.** It is the join of the two normal subgroups `E(G)`
(`layer_normal`) and `F(G)` (`fittingSubgroup_normal`). -/
theorem genFittingSubgroup_normal (G : Type*) [Group G] :
    (genFittingSubgroup G).Normal := by
  haveI := layer_normal (G := G)
  haveI := fittingSubgroup_normal G
  exact Subgroup.sup_normal (layer G) (fittingSubgroup G)

end FiniteSimpleGroups

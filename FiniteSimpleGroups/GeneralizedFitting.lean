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
* `genFittingSubgroup_eq_layer_of_fittingSubgroup_eq_bot` /
  `..._eq_fittingSubgroup_of_layer_eq_bot` — the degenerate cases (e.g. the
  B-theorem reduction `F(G) = 1 ⟹ F*(G) = E(G)`).
* `genFittingSubgroup_self_centralizing` (**axiom**, finite `G`) — Bender's
  cornerstone `C_G(F*(G)) ≤ F*(G)`; and its corollary
  `centralizer_genFittingSubgroup_eq_center` (`C_G(F*(G)) = Z(F*(G))`).
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

/-- If the Fitting subgroup is trivial then `F*(G) = E(G)`. This is the shape of the
**B-theorem reduction**: once `F(G) = 1`, the generalized Fitting subgroup collapses
to the layer, a (central) product of quasisimple components. -/
theorem genFittingSubgroup_eq_layer_of_fittingSubgroup_eq_bot
    (h : fittingSubgroup G = ⊥) : genFittingSubgroup G = layer G := by
  rw [genFittingSubgroup, h, sup_bot_eq]

/-- If the layer is trivial then `F*(G) = F(G)` — the soluble case, where the
generalized Fitting subgroup is just the ordinary Fitting subgroup. -/
theorem genFittingSubgroup_eq_fittingSubgroup_of_layer_eq_bot
    (h : layer G = ⊥) : genFittingSubgroup G = fittingSubgroup G := by
  rw [genFittingSubgroup, h, bot_sup_eq]

/-- **Bender's theorem — the cornerstone of the theory of the generalized Fitting
subgroup.** In any finite group, `F*(G)` is *self-centralizing*:
`C_G(F*(G)) ≤ F*(G)`. Equivalently `C_G(F*(G)) = Z(F*(G))`
(`centralizer_genFittingSubgroup_eq_center`).

This is what makes `F*(G)` the load-bearing object of the local theory: the action
of `G` on `F*(G)` by conjugation is faithful modulo the center, so
`G/Z(F*(G)) ↪ Aut(F*(G))` and the structure of `G` is controlled by `F*(G)`. It is
the generalized-Fitting analogue of the elementary fact `C_G(F(G)) ≤ F(G)` for
*soluble* `G`, extended past solubility by the layer.

Declared as an `axiom`: the proof (Aschbacher, *Finite Group Theory* 31.13; or
Kurzweil-Stellmacher 6.5.8) rests on `[E(G), F(G)] = 1` and the central-product
structure of `E(G)` — a chunk of local group theory well beyond this scaffold.
Following the repository's convention (cf. `Classification.CFSG`, the
`ProofStrategy` milestones), an honest dependency declaration rather than a
`sorry`. -/
axiom genFittingSubgroup_self_centralizing (G : Type*) [Group G] [Finite G] :
    Subgroup.centralizer (genFittingSubgroup G : Set G) ≤ genFittingSubgroup G

/-- **`C_G(F*(G)) = Z(F*(G))`.** The centralizer of the generalized Fitting subgroup
is exactly its center, realized in `G` as `F*(G) ⊓ C_G(F*(G))`. The `≥` inclusion is
trivial; the `≤` inclusion is precisely Bender's cornerstone
(`genFittingSubgroup_self_centralizing`). -/
theorem centralizer_genFittingSubgroup_eq_center (G : Type*) [Group G] [Finite G] :
    Subgroup.centralizer (genFittingSubgroup G : Set G)
      = genFittingSubgroup G ⊓ Subgroup.centralizer (genFittingSubgroup G : Set G) :=
  (le_inf (genFittingSubgroup_self_centralizing G) le_rfl).antisymm inf_le_right

end FiniteSimpleGroups

import FiniteSimpleGroups.ComponentStructure
import FiniteSimpleGroups.GeneralizedFitting

/-!
# The central-product structure of `E(G)` and `[E(G), F(G)] = 1`

The two structural facts that make `F*(G) = E(G)·F(G)` a *central product* — and that
feed Bender's cornerstone (`genFittingSubgroup_self_centralizing`):

* **distinct components commute** (`IsComponent.commute_of_ne`, Aschbacher 31.4): so
  `E(G)`, the join of the components, is a central product of quasisimple groups;
* **the layer centralizes the Fitting subgroup** (`layer_commutator_fittingSubgroup_eq_bot`,
  Kurzweil-Stellmacher 6.5.2): `[E(G), F(G)] = 1`.

Both are declared as `axiom`s, **explicitly tagged for discharge** once the Wielandt
subnormal-join theory (`⟨L, M⟩` of two subnormal subgroups is subnormal) is in place:
that is exactly the missing step between the *proven* `IsComponent.inf_le_center_of_ne`
(distinct components meet centrally) and the full `[L, M] = 1`. See `Wielandt.lean` for
the discharge effort. They follow the repository's honest-dependency convention (cf.
`genFittingSubgroup_self_centralizing`, `Classification.CFSG`).

From each axiom we derive its centralizer reformulation as a real theorem.

## Main results

* `IsComponent.commute_of_ne` (axiom) + `IsComponent.le_centralizer_of_ne`.
* `layer_commutator_fittingSubgroup_eq_bot` (axiom) + `layer_le_centralizer_fittingSubgroup`.
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

/-- **Distinct components commute** (Aschbacher, *Finite Group Theory* 31.4).

`axiom` pending the Wielandt subnormal-join theorem: the proven half is
`IsComponent.inf_le_center_of_ne` (the intersection `M ⊓ L` is central in `↥L`); the
remaining step deduces `⁅L, M⁆ ≤ L ⊓ M` from mutual subnormality and finishes with the
three-subgroups lemma and the perfectness `⁅L, L⁆ = L`. -/
axiom IsComponent.commute_of_ne [Finite G] {L M : Subgroup G}
    (hL : IsComponent L) (hM : IsComponent M) (hne : L ≠ M) : ⁅L, M⁆ = ⊥

/-- Distinct components centralize one another — the centralizer reformulation of
`IsComponent.commute_of_ne`. -/
theorem IsComponent.le_centralizer_of_ne [Finite G] {L M : Subgroup G}
    (hL : IsComponent L) (hM : IsComponent M) (hne : L ≠ M) :
    L ≤ Subgroup.centralizer (M : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hL.commute_of_ne hM hne)

/-- **The layer centralizes the Fitting subgroup**, `[E(G), F(G)] = 1`
(Kurzweil-Stellmacher, *The Theory of Finite Groups* 6.5.2). A component is perfect
and subnormal, so it centralizes every nilpotent normal subgroup; joining over the
components gives `[E(G), F(G)] = 1`.

`axiom` pending the same subnormal-action theory as `IsComponent.commute_of_ne`. -/
axiom layer_commutator_fittingSubgroup_eq_bot [Finite G] :
    ⁅layer G, fittingSubgroup G⁆ = ⊥

/-- The layer lies in the centralizer of the Fitting subgroup — the centralizer
reformulation of `layer_commutator_fittingSubgroup_eq_bot`. -/
theorem layer_le_centralizer_fittingSubgroup [Finite G] :
    layer G ≤ Subgroup.centralizer (fittingSubgroup G : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp layer_commutator_fittingSubgroup_eq_bot

end FiniteSimpleGroups

import FiniteSimpleGroups.AschbacherDichotomy
import FiniteSimpleGroups.GeneralizedFitting

/-!
# The central-product structure of `E(G)` and `[E(G), F(G)] = 1`

The two structural facts that make `F*(G) = E(G)·F(G)` a *central product* — and that
feed Bender's cornerstone (`genFittingSubgroup_self_centralizing`):

* **distinct components commute** (`IsComponent.commute_of_ne`, Aschbacher 31.4): so
  `E(G)`, the join of the components, is a central product of quasisimple groups;
* **the layer centralizes the Fitting subgroup** (`layer_commutator_fittingSubgroup_eq_bot`,
  Kurzweil-Stellmacher 6.5.2): `[E(G), F(G)] = 1`.

Both are now **theorems** — and the cluster is **fully axiom-free** (no Wielandt join).
They route through the component-vs-subnormal *dichotomy* `IsComponent.subnormal_dichotomy`
(Aschbacher 31.4: a component `L` and a subnormal `H` satisfy `L ≤ H ∨ ⁅L, H⁆ = ⊥`),
proved without the Wielandt join in `AschbacherDichotomy.lean` (a *forward* induction along
`H`'s subnormal chain replaces the classical normal-closure argument — found by Aristotle,
ported there; see `ARISTOTLE-JOB-components-commute.md`). `commute_of_ne` excludes the
`L ≤ M` branch via `eq_of_le`; `layer_commutator_fittingSubgroup_eq_bot` excludes it via
nilpotency of `F(G)`. The repository's earlier belief that this needed the Wielandt join
was simply too pessimistic.

## Main results

* `IsComponent.subnormal_dichotomy` (**theorem**, axiom-free, in `AschbacherDichotomy.lean`)
  ⟹ `IsComponent.commute_of_ne` (**theorem**) + `IsComponent.le_centralizer_of_ne`.
* `layer_commutator_fittingSubgroup_eq_bot` (**theorem**, also via the dichotomy) +
  `layer_le_centralizer_fittingSubgroup`.
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

open Subgroup

/-- **Distinct components commute** (Aschbacher, *Finite Group Theory* 31.4).

**Theorem.** A second component `M` is subnormal, so `subnormal_dichotomy` gives
`L ≤ M` or `⁅L, M⁆ = ⊥`. The first is impossible (`eq_of_le` would force `L = M`),
leaving `⁅L, M⁆ = ⊥`. -/
theorem IsComponent.commute_of_ne [Finite G] {L M : Subgroup G}
    (hL : IsComponent L) (hM : IsComponent M) (hne : L ≠ M) : ⁅L, M⁆ = ⊥ := by
  rcases hL.subnormal_dichotomy hM.isSubnormal with hle | hcomm
  · exact absurd (hL.eq_of_le hM hle) hne
  · exact hcomm

/-- Distinct components centralize one another — the centralizer reformulation of
`IsComponent.commute_of_ne`. -/
theorem IsComponent.le_centralizer_of_ne [Finite G] {L M : Subgroup G}
    (hL : IsComponent L) (hM : IsComponent M) (hne : L ≠ M) :
    L ≤ Subgroup.centralizer (M : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hL.commute_of_ne hM hne)

/-- **The layer centralizes the Fitting subgroup**, `[E(G), F(G)] = 1`
(Kurzweil-Stellmacher, *The Theory of Finite Groups* 6.5.2).

**Theorem** (discharged via `subnormal_dichotomy`): `F(G)` is normal, hence subnormal,
so each component `L` satisfies `L ≤ F(G)` or `⁅L, F(G)⁆ = ⊥`. The first is impossible —
`F(G)` is nilpotent (Fitting's theorem) hence solvable, so a subgroup `↥L` of it would be
solvable, contradicting that the quasisimple `↥L` is perfect and nontrivial
(`IsPerfect.not_isSolvable`). So `⁅L, F(G)⁆ = ⊥` for every component, and joining over the
components (`layer_le`) gives `⁅E(G), F(G)⁆ = ⊥`. -/
theorem layer_commutator_fittingSubgroup_eq_bot [Finite G] :
    ⁅layer G, fittingSubgroup G⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  apply layer_le
  intro L hL
  haveI := hL.isQuasisimple
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  rcases hL.subnormal_dichotomy (fittingSubgroup_normal G).isSubnormal_top with hLF | hcomm
  · exfalso
    haveI : Group.IsNilpotent (fittingSubgroup G) := fittingSubgroup_isNilpotent G
    have e := Subgroup.subgroupOfEquivOfLe hLF
    haveI : IsSolvable (L.subgroupOf (fittingSubgroup G)) := inferInstance
    have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
    haveI : IsSolvable L := solvable_of_solvable_injective hinj
    haveI : Nontrivial L := IsQuasisimple.nontrivial L
    haveI : Group.IsPerfect L := ⟨IsQuasisimple.commutator_eq_top L⟩
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · exact hcomm

/-- The layer lies in the centralizer of the Fitting subgroup — the centralizer
reformulation of `layer_commutator_fittingSubgroup_eq_bot`. -/
theorem layer_le_centralizer_fittingSubgroup [Finite G] :
    layer G ≤ Subgroup.centralizer (fittingSubgroup G : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp layer_commutator_fittingSubgroup_eq_bot

end FiniteSimpleGroups

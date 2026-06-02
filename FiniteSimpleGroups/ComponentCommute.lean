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

`commute_of_ne` is now a **theorem**, discharged onto the sharper axiom
`IsComponent.normalizes_of_ne` ("distinct components normalize one another"). That
axiom isolates the *one* fact still needing the Wielandt subnormal-join / normal-closure
theory (the classical proof runs through `⟨L^M⟩`); the commutator collapse on top of it —
three-subgroups lemma, perfectness `⁅L, L⁆ = L`, and the proven
`IsComponent.inf_le_center_of_ne` — is fully proven here. `layer_commutator_fittingSubgroup_eq_bot`
remains an axiom pending the same join theory. See `Wielandt.lean` for the discharge
effort; both follow the repository's honest-dependency convention (cf.
`genFittingSubgroup_self_centralizing`, `Classification.CFSG`).

## Main results

* `IsComponent.normalizes_of_ne` (axiom — the irreducible core) ⟹
  `IsComponent.commute_of_ne` (**theorem**) + `IsComponent.le_centralizer_of_ne`.
* `layer_commutator_fittingSubgroup_eq_bot` (axiom) + `layer_le_centralizer_fittingSubgroup`.
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

open Subgroup

/-- **Distinct components normalize one another** — the irreducible core of
"distinct components commute" (Aschbacher, *Finite Group Theory* 31.4).

This is the single fact `commute_of_ne` now rests on, and the *only* piece that
needs the Wielandt subnormal-join / normal-closure theory (the classical proof
runs through the normal closure `⟨L^M⟩`). Everything downstream of it — the
commutator collapse `⁅L, M⁆ = ⊥` — is a *theorem* below.

`axiom` pending that join theory (see `Wielandt.lean`). Sharper than the previous
`commute_of_ne` axiom: an `exact?` over the existing subnormal machinery cannot
close it, confirming it is genuinely the missing input rather than a packaging
gap. -/
axiom IsComponent.normalizes_of_ne [Finite G] {L M : Subgroup G}
    (hL : IsComponent L) (hM : IsComponent M) (hne : L ≠ M) : M ≤ normalizer L

/-- **Distinct components commute** (Aschbacher, *Finite Group Theory* 31.4).

**Theorem** (discharged from axiom): from `normalizes_of_ne` (applied both ways) we
get `⁅L, M⁆ ≤ M ⊓ L`; the proven `inf_le_center_of_ne` puts `M ⊓ L` in `C_G(L)`, so
`⁅⁅L, M⁆, L⁆ = 1`; the three-subgroups lemma plus the perfectness `⁅L, L⁆ = L` of the
quasisimple component then force `⁅L, M⁆ = 1`. -/
theorem IsComponent.commute_of_ne [Finite G] {L M : Subgroup G}
    (hL : IsComponent L) (hM : IsComponent M) (hne : L ≠ M) : ⁅L, M⁆ = ⊥ := by
  haveI := hL.isQuasisimple
  have hML : M ≤ normalizer L := hL.normalizes_of_ne hM hne
  have hLM : L ≤ normalizer M := hM.normalizes_of_ne hL hne.symm
  have hLcomm : ⁅M, L⁆ ≤ L := by
    rw [commutator_le]; intro m hm l hl
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hML hm) l).mp hl) (inv_mem hl)
  have hMcomm : ⁅L, M⁆ ≤ M := by
    rw [commutator_le]; intro l hl m hm
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hLM hl) m).mp hm) (inv_mem hm)
  have hLM_le_L : ⁅L, M⁆ ≤ L := by rw [Subgroup.commutator_comm]; exact hLcomm
  have h_inf : ⁅L, M⁆ ≤ M ⊓ L := le_inf hMcomm hLM_le_L
  have hcent : (M ⊓ L : Subgroup G) ≤ centralizer (L : Set G) := by
    intro x hx
    have hxL : x ∈ L := (mem_inf.mp hx).2
    have hc := hL.inf_le_center_of_ne hM hne (mem_subgroupOf.mpr hx :
      (⟨x, hxL⟩ : L) ∈ (M ⊓ L).subgroupOf L)
    rw [mem_centralizer_iff]
    intro h hh
    exact (by simpa using congrArg (Subtype.val) (mem_center_iff.mp hc ⟨h, hh⟩))
  have hrot : ⁅⁅L, M⁆, L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (h_inf.trans hcent)
  have hperf : ⁅L, L⁆ = L := by
    have h2 := congrArg (Subgroup.map L.subtype) (IsQuasisimple.commutator_eq_top (L : Type _))
    simp only [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    exact h2
  have h3 : ⁅⁅L, L⁆, M⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hrot
      (by rw [Subgroup.commutator_comm M L]; exact hrot)
  rwa [hperf] at h3

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

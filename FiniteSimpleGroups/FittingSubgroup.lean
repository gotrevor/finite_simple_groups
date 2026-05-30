import Mathlib

/-!
# The Fitting subgroup `F(G)` — a foundational brick mathlib lacks

Solomon's history (Bulletin AMS 38, 2001, p. 343) frames the whole CFSG
architecture through the **generalized Fitting subgroup** `F*(G) = E(G)·F(G)`:

* B-Theorem ⟹ `F(G) = 1`, so `F*(G) = E(G)` (a product of simple groups);
* Component Theorem ⟹ `F*(G)` is a *single* simple group;
* CFSG ⟹ classify all `G` with `F*(G)` nonabelian simple.

So `F(G)` (and then `F*(G)`) is the object the entire proof hangs on. mathlib
(v4.29.1) has **no group-theoretic Fitting subgroup** — every `Fitting` in the
library is the Lie-algebra / module Fitting *decomposition*, a different notion.
This file defines the ordinary Fitting subgroup and proves what's reachable.

## What's real vs. cited here

* `fittingSubgroup` — the definition (join of normal nilpotent subgroups).
* `normal_nilpotent_le_fittingSubgroup` — **proved** (universal property,
  `le_sSup`).
* `center_le_fittingSubgroup` — **proved** (center is normal + abelian ⇒
  nilpotent ⇒ inside `F(G)`). The first concrete fact about `F(G)`.
* `fittingSubgroup_normal`, `fittingSubgroup_isNilpotent` (**Fitting's Theorem**)
  — stated as cited `axiom`s. Fitting's Theorem (the join of normal nilpotent
  subgroups of a finite group is nilpotent) needs the lemma "the product of two
  normal nilpotent subgroups is nilpotent," which mathlib does **not** have.
  Discharging these is the next real piece of work.
  (Ref: Isaacs, *Finite Group Theory*, Thm 9.8; Kurzweil–Stellmacher §6.)
-/

namespace FiniteSimpleGroups

open scoped IsMulCommutative

/-- The **Fitting subgroup** `F(G)`: the supremum (join) of all normal
nilpotent subgroups of `G`.

For a finite group this is itself a normal nilpotent subgroup — the unique
*largest* one (Fitting's Theorem, `fittingSubgroup_isNilpotent` below). -/
def fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {H : Subgroup G | H.Normal ∧ Group.IsNilpotent H}

/-- **Universal property.** Every normal nilpotent subgroup lies in `F(G)`.
Immediate from the definition as a supremum. -/
theorem normal_nilpotent_le_fittingSubgroup {G : Type*} [Group G]
    (H : Subgroup G) (hN : H.Normal) (hnil : Group.IsNilpotent H) :
    H ≤ fittingSubgroup G :=
  le_sSup ⟨hN, hnil⟩

/-- The **center is contained in the Fitting subgroup**: it is normal and
abelian, hence nilpotent. A complete proof — the first concrete fact about
`F(G)`, and a sanity check that the definition behaves. -/
theorem center_le_fittingSubgroup {G : Type*} [Group G] :
    Subgroup.center G ≤ fittingSubgroup G :=
  normal_nilpotent_le_fittingSubgroup (Subgroup.center G) inferInstance
    CommGroup.isNilpotent

/-! ## Toward discharging Fitting's Theorem

The path to `fittingSubgroup_isNilpotent` runs through the finite-group
nilpotency TFAE (`isNilpotent_of_finite_tfae`): a finite group is nilpotent iff
all its Sylow subgroups are normal. The bricks below are the first verified
steps. mathlib has **no `pCore`/`O_p`**, so the `O_p`-decomposition route is
built by hand from these. -/

/-- In a finite **nilpotent** group every Sylow subgroup is characteristic.
Chain: nilpotent ⇒ normalizer condition ⇒ Sylow normal ⇒ Sylow characteristic.
First verified brick toward Fitting's Theorem. -/
theorem sylow_characteristic_of_isNilpotent {N : Type*} [Group N] [Finite N]
    [Group.IsNilpotent N] {p : ℕ} [Fact p.Prime] (P : Sylow p N) :
    (↑P : Subgroup N).Characteristic :=
  P.characteristic_of_normal
    (P.normal_of_normalizerCondition normalizerCondition_of_isNilpotent)

/-- **Sylow subgroups of a normal nilpotent subgroup are normal in the whole
group.** If `N ⊴ G` is nilpotent, its (unique) Sylow `p`-subgroup is
characteristic in `N` (`sylow_characteristic_of_isNilpotent`), and a
characteristic subgroup of a normal subgroup is normal in `G`
(`IsConjugate.normal_of_characteristic_of_normal`). Second brick. -/
theorem sylow_normal_of_normal_nilpotent {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent N)
    {p : ℕ} [Fact p.Prime] (P : Sylow p N) :
    ((↑P : Subgroup N).map N.subtype).Normal := by
  haveI := hN
  haveI := hnil
  haveI := sylow_characteristic_of_isNilpotent P
  infer_instance

/-- A **normal `p`-subgroup lies inside `F(G)`.** A finite `p`-group is nilpotent
(`IsPGroup.isNilpotent`), so a normal `p`-subgroup is normal nilpotent and the
universal property places it in `F(G)`. Third brick — this is what makes the
(hand-rolled) `p`-core a subgroup of `F(G)`. -/
theorem normal_pgroup_le_fittingSubgroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} {Q : Subgroup G} (hQ : Q.Normal) (hp : IsPGroup p Q) :
    Q ≤ fittingSubgroup G :=
  normal_nilpotent_le_fittingSubgroup Q hQ hp.isNilpotent

/-- **Fitting's Theorem (normality half).** `F(G)` is a normal subgroup.
Cited; mathlib lacks the join-of-normals-is-normal lemma in usable form here. -/
axiom fittingSubgroup_normal (G : Type*) [Group G] : (fittingSubgroup G).Normal

/-- **Fitting's Theorem (nilpotency half).** For a finite group, `F(G)` is
nilpotent — hence the unique largest normal nilpotent subgroup. Cited (Isaacs
Thm 9.8); needs "product of normal nilpotent subgroups is nilpotent," absent
from mathlib v4.29.1. Discharging this is the headline next step. -/
axiom fittingSubgroup_isNilpotent (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent (fittingSubgroup G)

end FiniteSimpleGroups

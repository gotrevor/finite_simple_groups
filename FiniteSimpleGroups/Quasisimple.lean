import Mathlib

/-!
# Quasisimple groups — the building block of the layer `E(G)`

Solomon's history (Bulletin AMS 38, 2001, p. 343) builds the whole CFSG
architecture on the **generalized Fitting subgroup** `F*(G) = E(G)·F(G)`, where
`F(G)` is the Fitting subgroup (built in `FittingSubgroup.lean`) and `E(G)` is the
**layer**: the join of the *components* of `G`. A component is a subnormal
*quasisimple* subgroup, so quasisimple groups are the atoms `E(G)` is assembled
from.

A group `Q` is **quasisimple** when it is *perfect* (`⁅Q, Q⁆ = Q`) and the central
quotient `Q / Z(Q)` is *simple*. Equivalently, `Q` is a perfect central extension
of a simple group. The two leading examples:

* every **nonabelian simple** group is quasisimple (`isQuasisimple_of_isSimpleGroup`);
* the special linear groups `SL(n, q)` are quasisimple for most `n, q`
  (a central extension of `PSL(n, q)`), even when not simple.

mathlib (v4.29.1) has **no notion of quasisimple group** — `IsSimpleGroup` and
`Group.IsPerfect` exist, but not their conjunction-through-the-center. This file
introduces it and proves the basic facts reachable without subnormality theory
(which mathlib also lacks; that is the next brick toward `E(G)`).

`open Subgroup` is deliberately *not* used here: `⁅·,·⁆` already names
`Subgroup.commutator`, so opening the namespace shadows the top-level group
`commutator G` and breaks name resolution (mathlib's own commutator file uses
`open Subgroup hiding commutator` for the same reason).
-/

namespace FiniteSimpleGroups

open Subgroup (center centralizer)

/-- A group `Q` is **quasisimple** if it is perfect and its central quotient
`Q / Z(Q)` is simple. -/
class IsQuasisimple (Q : Type*) [Group Q] : Prop where
  /-- A quasisimple group is perfect: `⁅Q, Q⁆ = Q`. -/
  isPerfect : Group.IsPerfect Q
  /-- The central quotient of a quasisimple group is simple. -/
  isSimpleGroup_quotient_center : IsSimpleGroup (Q ⧸ center Q)

namespace IsQuasisimple

/-- A quasisimple group equals its own commutator subgroup. -/
theorem commutator_eq_top (Q : Type*) [Group Q] [h : IsQuasisimple Q] :
    commutator Q = ⊤ :=
  h.isPerfect.commutator_eq_top

/-- A quasisimple group is nontrivial: its central quotient is simple, hence
nontrivial, and a nontrivial quotient forces the group itself to be nontrivial. -/
theorem nontrivial (Q : Type*) [Group Q] [h : IsQuasisimple Q] : Nontrivial Q := by
  haveI := h.isSimpleGroup_quotient_center
  haveI : Nontrivial (Q ⧸ center Q) := inferInstance
  exact (QuotientGroup.mk'_surjective (center Q)).nontrivial

end IsQuasisimple

/-- `⁅G, G⁆ = ⊥ ↔ Z(G) = ⊤`. mathlib proves this
(`commutator_eq_bot_iff_center_eq_top`) but in a `module`-system file that does not
export it by name downstream; its public ingredient
`Subgroup.commutator_eq_bot_iff_le_centralizer` lets us reconstruct it verbatim:
`⁅⊤, ⊤⁆ = ⊥ ↔ ⊤ ≤ C(⊤) = Z(G)`, and `⊤ ≤ Z(G) ↔ Z(G) = ⊤`. -/
private theorem commutator_eq_bot_iff_center_eq_top {G : Type*} [Group G] :
    commutator G = ⊥ ↔ center G = ⊤ := by
  unfold commutator
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
    Subgroup.centralizer_univ, top_le_iff]

/-- **Nonabelian simple groups are quasisimple.** For a simple group `G` the
center is normal, so it is `⊥` or `⊤`; "nonabelian" (`Z(G) ≠ ⊤`) forces `Z(G) = ⊥`.
Then:

* `G` is **perfect** — its commutator is normal, hence `⊥` or `⊤`; were it `⊥`
  the center would be `⊤` (`commutator_eq_bot_iff_center_eq_top`), contradicting
  nonabelianness, so `⁅G, G⁆ = ⊤`;
* `G / Z(G) ≃* G / ⊥ ≃* G` is **simple**, transporting `G`'s simplicity across the
  isomorphism. -/
theorem isQuasisimple_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : center G ≠ ⊤) : IsQuasisimple G := by
  -- the center of a nonabelian simple group is trivial
  have hc : center G = ⊥ :=
    ((inferInstance : (center G).Normal).eq_bot_or_eq_top).resolve_right hna
  refine ⟨?_, ?_⟩
  · -- `G` is perfect
    rw [Group.isPerfect_def]
    rcases (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with hb | ht
    · exact absurd (commutator_eq_bot_iff_center_eq_top.mp hb) hna
    · exact ht
  · -- `G / Z(G)` is simple
    haveI : IsSimpleGroup (G ⧸ (⊥ : Subgroup G)) := QuotientGroup.quotientBot.isSimpleGroup
    exact (QuotientGroup.quotientMulEquivOfEq hc).isSimpleGroup

end FiniteSimpleGroups

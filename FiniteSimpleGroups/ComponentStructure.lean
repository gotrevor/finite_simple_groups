import FiniteSimpleGroups.LayerNormal

/-!
# Structure of quasisimple groups and components

The deep structural facts behind `[E(G), F(G)] = 1` and "E(G) is a central product
of its components" all rest on one intrinsic property of a quasisimple group `Q`:

> **Every normal subgroup of `Q` is central or the whole group.**

(`Z(Q)` is the unique maximal normal subgroup, because `Q/Z(Q)` is simple and `Q` is
perfect.) Iterating up a subnormal chain extends this to subnormal subgroups. These
are the technical heart that distinguishes a *component* (subnormal quasisimple) from
an arbitrary subgroup, and mathlib has none of it (it has no notion of quasisimple).

## Main results

* `IsQuasisimple.normal_le_center_or_eq_top` — a normal subgroup of a quasisimple
  group is `≤ Z(Q)` or `= ⊤`.
* `IsQuasisimple.subnormal_le_center_or_eq_top` — the same for *subnormal* subgroups
  (by induction up the chain).

These results would sit naturally in `Quasisimple.lean`; they live here to keep the
per-brick branch stack clean (they are downstream of `LayerNormal`'s
`isNormalStep_iff_le_normalizer`).
-/

namespace FiniteSimpleGroups

open Subgroup (center)

/-- **In a quasisimple group, a normal subgroup is central or everything.**
The image of `N` in the simple group `Q ⧸ Z(Q)` is normal, hence `⊥` (so `N ≤ Z(Q)`)
or `⊤` (so `N ⊔ Z(Q) = ⊤`; then since `Z(Q)` is abelian and `Q` is perfect,
`commutator Q = ⊤ ≤ N`, forcing `N = ⊤`). -/
theorem IsQuasisimple.normal_le_center_or_eq_top {Q : Type*} [Group Q] [hQ : IsQuasisimple Q]
    {N : Subgroup Q} (hN : N.Normal) : N ≤ center Q ∨ N = ⊤ := by
  haveI := hQ.isSimpleGroup_quotient_center
  haveI hNmap : (N.map (QuotientGroup.mk' (center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hNmap.eq_bot_or_eq_top with hbot | htop
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  · right
    have hsup : N ⊔ center Q = ⊤ := by
      have h := congrArg (Subgroup.comap (QuotientGroup.mk' (center Q))) htop
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [IsQuasisimple.commutator_eq_top Q] at hcomm
    exact top_le_iff.mp hcomm

/-- Auxiliary for `subnormal_le_center_or_eq_top`: induct up the subnormal chain,
carrying `K = ⊤` as a hypothesis so the `ReflTransGen` recursion can generalize the
top of the chain. -/
private theorem subnormal_aux {Q : Type*} [Group Q] [IsQuasisimple Q] {N K : Subgroup Q}
    (h : IsSubnormal N K) : K = ⊤ → N ≤ center Q ∨ N = ⊤ := by
  induction h with
  | refl => intro hK; exact Or.inr hK
  | @tail c K' hNc hstep ih =>
    intro hK
    subst hK
    have hcN : c.Normal :=
      Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp (isNormalStep_iff_le_normalizer.mp hstep).2)
    rcases IsQuasisimple.normal_le_center_or_eq_top hcN with hc | hc
    · exact Or.inl ((IsSubnormal.le hNc).trans hc)
    · exact ih hc

/-- **In a quasisimple group, a subnormal subgroup is central or everything.**
Iterating `normal_le_center_or_eq_top` up the subnormal chain: the top link is normal
in `Q`, so it is central (whence everything below it is) or all of `Q` (whence the
shorter chain finishes by induction). This is the property that makes a *component*
(subnormal quasisimple) rigid. -/
theorem IsQuasisimple.subnormal_le_center_or_eq_top {Q : Type*} [Group Q] [IsQuasisimple Q]
    {N : Subgroup Q} (hN : IsSubnormal N ⊤) : N ≤ center Q ∨ N = ⊤ :=
  subnormal_aux hN rfl

variable {G : Type*} [Group G]

/-- **A normal step meets a subgroup `H` in a normal step.** If `A ⊴ B` then
`A ⊓ H ⊴ B ⊓ H`: an element of `B ⊓ H` normalizes `A` (it lies in `B`) and `H` (it
lies in `H`), hence normalizes `A ⊓ H`. -/
theorem IsNormalStep.inf_right {A B : Subgroup G} (h : IsNormalStep A B) (H : Subgroup G) :
    IsNormalStep (A ⊓ H) (B ⊓ H) := by
  rw [isNormalStep_iff_le_normalizer] at h ⊢
  obtain ⟨hAB, hnorm⟩ := h
  refine ⟨inf_le_inf_right H hAB, fun x hx => ?_⟩
  obtain ⟨hxB, hxH⟩ := Subgroup.mem_inf.mp hx
  have hxA := Subgroup.mem_normalizer_iff.mp (hnorm hxB)
  have hxnH := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxH)
  rw [Subgroup.mem_normalizer_iff]
  intro n
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hxA n, hxnH n]

/-- **Subnormality is preserved by meeting with a subgroup.** If `A` is subnormal in
`K` then `A ⊓ H` is subnormal in `K ⊓ H` — intersect every link of the chain with
`H`. -/
theorem IsSubnormal.inf_right {A K : Subgroup G} (h : IsSubnormal A K) (H : Subgroup G) :
    IsSubnormal (A ⊓ H) (K ⊓ H) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | @tail c K' _ hstep ih => exact ih.tail (hstep.inf_right H)

/-- A subnormal subgroup of the whole group meets any `H` in a subnormal subgroup of
`H` (the case `K = ⊤`). -/
theorem IsSubnormal.inf_top_right {M : Subgroup G} (h : IsSubnormal M ⊤) (H : Subgroup G) :
    IsSubnormal (M ⊓ H) H := by
  have h2 := h.inf_right H
  rwa [top_inf_eq] at h2

end FiniteSimpleGroups

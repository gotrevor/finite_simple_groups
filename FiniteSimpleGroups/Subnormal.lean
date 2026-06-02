import Mathlib

/-!
# Subnormal subgroups — the missing primitive under `E(G)`

A subgroup `H` of `G` is **subnormal** when there is a finite chain
`H = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₙ = G`, each term normal in the *next* (not necessarily in
`G`). This is strictly weaker than normality and is the relation the layer `E(G)`
is built on: a **component** of `G` is a subnormal *quasisimple* subgroup
(see `Quasisimple.lean`), and `E(G) = ⟨components⟩` (next brick).

mathlib (v4.29.1) has **no notion of subnormal subgroup** (`grep -ri subnormal`
finds only `subgroupOf`-flavoured names, nothing about chains). We supply it as the
reflexive-transitive closure of the one-step relation "`H ≤ K` with `H` normal in
`K`", reusing `Relation.ReflTransGen` so transitivity and induction come for free.

## Main definitions

* `IsNormalStep H K` — `H ≤ K` and `H` is normal in `K` (`(H.subgroupOf K).Normal`).
* `IsSubnormal H K` — `Relation.ReflTransGen IsNormalStep H K`: a finite ascending
  chain of normal steps from `H` up to `K`.

## Main results

* `IsSubnormal.refl`, `IsSubnormal.trans` — it is a preorder (reflexive, transitive).
* `IsNormalStep.isSubnormal` — a single normal step is subnormal.
* `IsSubnormal.le` — subnormal subgroups are contained in the ambient group.
* `Subgroup.Normal.isSubnormal_top` — a normal subgroup is subnormal in `G` (`⊤`).
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

/-- One link of a subnormal chain: `H ≤ K` with `H` **normal in `K`**
(`(H.subgroupOf K).Normal`). This is the "`H ⊴ K`" relation for `H ≤ K` not
necessarily comparable to the ambient group. -/
def IsNormalStep (H K : Subgroup G) : Prop :=
  H ≤ K ∧ (H.subgroupOf K).Normal

/-- `H` is **subnormal** in `K`: there is a finite chain
`H = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₙ = K`, each term normal in the next. Encoded as the
reflexive-transitive closure of `IsNormalStep`. -/
def IsSubnormal (H K : Subgroup G) : Prop :=
  Relation.ReflTransGen IsNormalStep H K

namespace IsNormalStep

/-- A normal step is in particular a containment. -/
theorem le {H K : Subgroup G} (h : IsNormalStep H K) : H ≤ K := h.1

/-- A normal step is normal: `H ⊴ K`. -/
theorem normal {H K : Subgroup G} (h : IsNormalStep H K) : (H.subgroupOf K).Normal := h.2

/-- A single normal step witnesses subnormality. -/
theorem isSubnormal {H K : Subgroup G} (h : IsNormalStep H K) : IsSubnormal H K :=
  Relation.ReflTransGen.single h

end IsNormalStep

/-- A subgroup that is `≤ K` and normal-in-`K` is a normal step into `K`. -/
theorem isNormalStep_of_normal {H K : Subgroup G} (hHK : H ≤ K)
    (hH : (H.subgroupOf K).Normal) : IsNormalStep H K :=
  ⟨hHK, hH⟩

namespace IsSubnormal

/-- Subnormality is reflexive. -/
@[refl]
theorem refl (H : Subgroup G) : IsSubnormal H H := Relation.ReflTransGen.refl

/-- Subnormality is transitive: stacking two subnormal chains gives one. -/
theorem trans {H K L : Subgroup G} (h₁ : IsSubnormal H K) (h₂ : IsSubnormal K L) :
    IsSubnormal H L := Relation.ReflTransGen.trans h₁ h₂

/-- A subnormal subgroup is contained in its ambient group. -/
theorem le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans hstep.le

/-- Extend a subnormal chain by one normal step at the top. -/
theorem tail {H K L : Subgroup G} (h : IsSubnormal H K) (hstep : IsNormalStep K L) :
    IsSubnormal H L := Relation.ReflTransGen.tail h hstep

end IsSubnormal

/-- **A normal subgroup is subnormal in the whole group.** `H ⊴ G` means
`H.Normal`; via `Normal.subgroupOf` it is normal in `⊤`, giving a one-step chain
`H ⊴ ⊤`. -/
theorem _root_.Subgroup.Normal.isSubnormal_top {H : Subgroup G} (hH : H.Normal) :
    IsSubnormal H ⊤ :=
  (isNormalStep_of_normal le_top (hH.subgroupOf ⊤)).isSubnormal

/-- The whole group is (trivially) subnormal in itself. -/
theorem isSubnormal_top_top : IsSubnormal (⊤ : Subgroup G) ⊤ := IsSubnormal.refl ⊤

/-- The trivial subgroup is subnormal in the whole group (it is normal). -/
theorem isSubnormal_bot_top : IsSubnormal (⊥ : Subgroup G) ⊤ :=
  (Subgroup.normal_bot).isSubnormal_top

/-- **The preimage of a subnormal subgroup is subnormal.** For a group homomorphism
`f : G →* G'`, if `B` is subnormal in `D` (in `G'`) then `comap f B` is subnormal in
`comap f D` (in `G`). Each normal step of the chain `B ◁ ⋯ ◁ D` is carried through `comap`
using `normal_subgroupOf_iff_le_normalizer` together with `le_normalizer_comap` (the
preimage of the normalizer sits inside the normalizer of the preimage); this mirrors
mathlib's `Subgroup.IsSubnormal.comap`. -/
theorem IsSubnormal.comap {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {B D : Subgroup G'} (h : IsSubnormal B D) :
    IsSubnormal (B.comap f) (D.comap f) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | tail _ hstep ih =>
    refine ih.tail ⟨Subgroup.comap_mono hstep.1, ?_⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.comap_mono hstep.1)]
    have hN := hstep.2
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hstep.1] at hN
    exact (Subgroup.comap_mono hN).trans (Subgroup.le_normalizer_comap f)

/-- **The preimage of a subnormal-in-`⊤` subgroup is subnormal in `⊤`.** Specialization of
`IsSubnormal.comap` with `D = ⊤` (`comap f ⊤ = ⊤`): if `B` is subnormal in `G'` then
`comap f B` is subnormal in `G`. This is the form used to pull a component of a quotient
back to the covering group. -/
theorem IsSubnormal.comap_top {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {B : Subgroup G'} (h : IsSubnormal B ⊤) :
    IsSubnormal (B.comap f) ⊤ := by
  have := h.comap f
  rwa [Subgroup.comap_top] at this

end FiniteSimpleGroups

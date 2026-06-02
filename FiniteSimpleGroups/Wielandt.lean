import FiniteSimpleGroups.Subnormal

/-!
# Wielandt's join theorem — warm-up: `IsSubnormal.sup_normal`

The **join theorem of Wielandt** states that the join of two subnormal subgroups
of a *finite* group is again subnormal. This file establishes the **warm-up**
`IsSubnormal.sup_normal` (proved), the case where one of the two subgroups is
actually normal:

  > If `H` is subnormal in `G` and `N ⊴ G`, then `H ⊔ N` is subnormal in `G`.

## The full Wielandt join is not needed by this scaffold

Earlier sessions carried the **full join** — the join of two arbitrary subnormal
subgroups is subnormal (over `[Finite G]`) — as an honest `axiom`, on the belief
that the Aschbacher 31.4 component-commuting dichotomy required it. That belief
turned out to be **too pessimistic**: Aristotle found a proof of the dichotomy
(`AschbacherDichotomy.lean`) that uses only a *forward* induction along `H`'s
subnormal chain (`centralizing_by_subnormal`) and never the full join. With the
dichotomy discharged join-free, nothing in the tree consumed the full-join axiom,
so it was removed (2026-06-02) rather than left as dead proof debt.

For the record, the full join is **false for arbitrary groups** (there exist
infinite groups with two subnormal subgroups whose join is not subnormal); it
holds under the maximal condition, in particular for finite groups, by a genuine
three-subgroups / repeated-commutator argument. Reference: H. Wielandt, *Eine
Verallgemeinerung der invarianten Untergruppen*, Math. Z. **45** (1939); Isaacs,
*Finite Group Theory*, Thm 2.13; Robinson, *A Course in the Theory of Groups*,
13.1.4. The warm-up below is the slice the scaffold actually uses.

The proof lifts a subnormal chain `H = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₙ = G` to the chain
`H ⊔ N ⊴ H₁ ⊔ N ⊴ ⋯ ⊴ G ⊔ N = G`. The single-step fact
(`isNormalStep_sup_right`) is: `A ⊴ B` and `N ⊴ G` ⟹ `A ⊔ N ⊴ B ⊔ N`, because

* `N ≤ A ⊔ N ≤ normalizer (A ⊔ N)` — any element of a subgroup normalizes it;
* each `b ∈ B` normalizes `A` (since `A ⊴ B`) and normalizes `N` (since `N ⊴ G`),
  hence the conjugation `ConjAct.toConjAct b` fixes `A ⊔ N` (it distributes over
  `⊔`), so `b` normalizes `A ⊔ N`.

Lifting along the reflexive-transitive closure is `Relation.ReflTransGen.lift`.

The pointwise conjugation action on `Subgroup G` is by `ConjAct G`
(`ConjAct.toConjAct g • H`); `Subgroup.conjAct_pointwise_smul_iff` is the bridge
between that and `g ∈ normalizer H`. Note `Subgroup.normalizer` takes a `Set G`,
so it is written applicatively (`normalizer (↑H)`), not via dot notation.

## Main results

* `isNormalStep_sup_right` — the single-step lift `A ⊴ B ⟹ A ⊔ N ⊴ B ⊔ N`.
* `IsSubnormal.sup_normal` — Wielandt warm-up:
  `IsSubnormal H ⊤ ⟹ IsSubnormal (H ⊔ N) ⊤`.
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

open scoped Pointwise

/-- **Single step of the Wielandt lift.** If `A ⊴ B` (a normal step) and `N ⊴ G`,
then `A ⊔ N ⊴ B ⊔ N`. -/
theorem isNormalStep_sup_right {A B N : Subgroup G} (h : IsNormalStep A B)
    (hN : N.Normal) : IsNormalStep (A ⊔ N) (B ⊔ N) := by
  haveI := h.2
  have hBA : B ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf h.1
  have hle : A ⊔ N ≤ B ⊔ N := sup_le_sup_right h.1 N
  refine ⟨hle, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  refine sup_le (fun b hb => ?_) (le_sup_right.trans Subgroup.le_normalizer)
  -- `b ∈ B` fixes `A ⊔ N` by conjugation: it fixes `A` and `N` separately.
  rw [← Subgroup.conjAct_pointwise_smul_iff, Subgroup.smul_sup,
    Subgroup.conjAct_pointwise_smul_eq_self (hBA hb), hN.conjAct (ConjAct.toConjAct b)]

/-- **Wielandt warm-up.** If `H` is subnormal in `G` and `N ⊴ G`, then `H ⊔ N` is
subnormal in `G`. -/
theorem IsSubnormal.sup_normal {H N : Subgroup G} (hH : IsSubnormal H ⊤)
    (hN : N.Normal) : IsSubnormal (H ⊔ N) ⊤ := by
  have key : IsSubnormal (H ⊔ N) (⊤ ⊔ N) :=
    Relation.ReflTransGen.lift (· ⊔ N)
      (fun _ _ hab => isNormalStep_sup_right hab hN) hH
  rwa [top_sup_eq] at key

end FiniteSimpleGroups

import FiniteSimpleGroups.Subnormal

/-!
# Wielandt's join theorem — warm-up: `IsSubnormal.sup_normal`

The **join theorem of Wielandt** states that the join of two subnormal subgroups
of a finite group is again subnormal. The full theorem needs the three-subgroups
lemma; this file establishes the **warm-up** that already powers the layer `E(G)`:

> If `H` is subnormal in `G` and `N ⊴ G`, then `H ⊔ N` is subnormal in `G`.

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

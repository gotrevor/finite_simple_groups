import FiniteSimpleGroups.Subnormal

/-!
# Wielandt's join theorem — warm-up: `IsSubnormal.sup_normal`

The **join theorem of Wielandt** states that the join of two subnormal subgroups
of a *finite* group is again subnormal. This file establishes:

* the **warm-up** `IsSubnormal.sup_normal` (proved), which already powers the
  layer `E(G)`:

  > If `H` is subnormal in `G` and `N ⊴ G`, then `H ⊔ N` is subnormal in `G`.

* the **full join** `IsSubnormal.sup` (declared as an `axiom` over `[Finite G]`).

## Why the full join is an axiom — and why it needs `[Finite G]`

Unlike the warm-up, the full join is **false for arbitrary groups**: there exist
(necessarily infinite) groups with two subnormal subgroups whose join is *not*
subnormal. Wielandt's theorem holds under the maximal condition on subgroups, in
particular for finite groups, and its proof is a genuine chunk of local group
theory (a three-subgroups / repeated-commutator argument; mathlib has no `sup`
lemma for its own `Subgroup.IsSubnormal`, only `inf`). Following the repository
convention for deep results beyond the current scaffold (cf. Bender's
`genFittingSubgroup_self_centralizing`, and the `Classification.CFSG` /
`ProofStrategy` milestones), it is recorded as an honest `axiom` under `[Finite G]`
rather than a `sorry`. Reference: H. Wielandt, *Eine Verallgemeinerung der
invarianten Untergruppen*, Math. Z. **45** (1939); textbook treatment in Isaacs,
*Finite Group Theory*, Thm 2.13, or Robinson, *A Course in the Theory of Groups*,
13.1.4.

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
* `IsSubnormal.sup` — Wielandt's full join theorem (`axiom`, `[Finite G]`):
  `IsSubnormal H ⊤ → IsSubnormal K ⊤ → IsSubnormal (H ⊔ K) ⊤`.
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

/-- **Wielandt's join theorem.** In a *finite* group, the join of two subnormal
subgroups is again subnormal.

This is **false without a finiteness/maximal-condition hypothesis** (there are
infinite groups where the join of two subnormals is not subnormal), and mathlib
provides no `sup` lemma for its own `Subgroup.IsSubnormal` (only `inf`). Its proof
is a real piece of local group theory beyond the present scaffold, so — following
the repository convention for such results (cf.
`genFittingSubgroup_self_centralizing`) — it is recorded as an honest `axiom`
under `[Finite G]` rather than a `sorry`. See the module docstring for references
(Wielandt 1939; Isaacs, *Finite Group Theory* 2.13). -/
axiom IsSubnormal.sup {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hH : IsSubnormal H ⊤) (hK : IsSubnormal K ⊤) : IsSubnormal (H ⊔ K) ⊤

end FiniteSimpleGroups

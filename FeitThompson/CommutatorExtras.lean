/-
# Commutator extras — mathlib bricks the FT port needs

Local axiomatization of small commutator / normalizer facts that MathComp
provides as one-liners but mathlib (v4.29.1) doesn't surface directly.
Each axiom cites the MathComp lemma it mirrors.

These belong upstream as separate mathlib PRs (small, self-contained, each
~50 LOC). Until then, they live here so BG §1 propositions can be stated
as real theorems instead of axioms.
-/

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

namespace FeitThompson.CommutatorExtras

variable {G : Type*} [Group G]

/-- **AXIOM** — sup-distribution of commutator (MathComp `commMG`).

For arbitrary subgroups `H`, `K`, `L` with `L` normalizing both `H` and `K`:
  `⁅H ⊔ K, L⁆ ≤ ⁅H, L⁆ ⊔ ⁅K, L⁆`.

Proof (sketch): induction on `H ⊔ K` via `Subgroup.closure_induction`, using
the identity `⁅xy, l⁆ = (y⁻¹ · ⁅x, l⁆ · y) · ⁅y, l⁆`. The normalization
hypotheses are what make the conjugated term `y⁻¹ ⁅x, l⁆ y` stay in
`⁅H, L⁆ ⊔ ⁅K, L⁆`.

MathComp source: `math-comp/algebra/commutator.v`, lemma `commMG` (with the
side condition discharged by `normsR`). The MathComp version proves equality
under stronger hypotheses; we only need `≤`. -/
axiom commutator_sup_le
    {G : Type*} [Group G]
    (H K L : Subgroup G)
    (_hLH : L ≤ Subgroup.normalizer ((H : Subgroup G) : Set G))
    (_hLK : L ≤ Subgroup.normalizer ((K : Subgroup G) : Set G)) :
    ⁅H ⊔ K, L⁆ ≤ ⁅H, L⁆ ⊔ ⁅K, L⁆

/-- **AXIOM** — the second argument of a commutator normalizes the
commutator subgroup (MathComp `commg_normr`).

For `H, A` subgroups of `G`: `A ≤ N(⁅H, A⁆)`.

Proof (sketch): conjugating a generator `⁅h, a⁆` by `a' ∈ A` yields
`⁅a'ha'⁻¹, a'aa'⁻¹⁆`. The first arg is in `H` only if `A` normalizes `H`;
in our use case `H = ⊤` so this is automatic. The second arg is in `A`
trivially. Closure under conjugation by `A` follows.

MathComp source: `math-comp/algebra/commutator.v`, lemma `commg_normr`. -/
axiom commg_normr
    {G : Type*} [Group G]
    (A : Subgroup G) :
    A ≤ Subgroup.normalizer ((⁅(⊤ : Subgroup G), A⁆ : Subgroup G) : Set G)

/-- Every subgroup normalizes its own centralizer (MathComp `cent_norm` /
`subset_norm_cent`).

For any subgroup `A`: `A ≤ N(C(A))`.

Proved directly: for `a ∈ A` and `x ∈ C(A)`, conjugation by `a` sends `x`
to `a*x*a⁻¹`. To show this is in `C(A)`, take `b ∈ A`. Since `A` is a
subgroup, `a⁻¹*b*a ∈ A`, so `x` commutes with it. Sandwiching by `a, a⁻¹`
gives `(a*x*a⁻¹) * b = b * (a*x*a⁻¹)`.

(Was Increment 11's third "extras" axiom; discharged at Inc 20 via direct
`mem_normalizer_iff` + `mem_centralizer_iff` unfolding + `group` tactic.) -/
theorem le_normalizer_centralizer
    {G : Type*} [Group G]
    (A : Subgroup G) :
    A ≤ Subgroup.normalizer
      ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hxC
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro b hb
    have hc : a⁻¹ * b * a ∈ A :=
      A.mul_mem (A.mul_mem (A.inv_mem ha) hb) ha
    have hcomm := hxC (a⁻¹ * b * a) hc
    have key : a * ((a⁻¹ * b * a) * x) * a⁻¹
             = a * (x * (a⁻¹ * b * a)) * a⁻¹ := by rw [hcomm]
    have lhs : a * ((a⁻¹ * b * a) * x) * a⁻¹ = b * (a * x * a⁻¹) := by group
    have rhs : a * (x * (a⁻¹ * b * a)) * a⁻¹ = (a * x * a⁻¹) * b := by group
    exact lhs.symm.trans (key.trans rhs)
  · intro hxC
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro b hb
    have hc : a * b * a⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)
    have hcomm := hxC (a * b * a⁻¹) hc
    have key : a⁻¹ * ((a*b*a⁻¹) * (a*x*a⁻¹)) * a
             = a⁻¹ * ((a*x*a⁻¹) * (a*b*a⁻¹)) * a := by rw [hcomm]
    have lhs : a⁻¹ * ((a*b*a⁻¹) * (a*x*a⁻¹)) * a = b * x := by group
    have rhs : a⁻¹ * ((a*x*a⁻¹) * (a*b*a⁻¹)) * a = x * b := by group
    exact lhs.symm.trans (key.trans rhs)

end FeitThompson.CommutatorExtras

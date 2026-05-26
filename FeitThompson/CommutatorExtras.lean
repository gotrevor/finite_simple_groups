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

/-- **AXIOM** — every subgroup normalizes its own centralizer
(MathComp `cent_norm` / `subset_norm_cent`).

For any subgroup `A`: `A ≤ N(C(A))`.

Proof (sketch): for `a ∈ A`, conjugation by `a` is an automorphism of `A`,
hence permutes elements of `A`. So if `x` commutes with every element of `A`,
so does `axa⁻¹`. Hence `axa⁻¹ ∈ C(A)`.

Mathlib has `Subgroup.le_normalizer : H ≤ N(H)`. The analog for "N(C(H))"
isn't immediately surfaced. MathComp source: derivable from `normsI` +
`cent_sub`. -/
axiom le_normalizer_centralizer
    {G : Type*} [Group G]
    (A : Subgroup G) :
    A ≤ Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G)

end FeitThompson.CommutatorExtras

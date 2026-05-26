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

/-- The second argument of a commutator normalizes the commutator subgroup
(MathComp `commg_normr`).

For `A` a subgroup of `G`: `A ≤ N(⁅⊤, A⁆)`.

Proved by closure-induction on `⁅⊤, A⁆`. For a generator `⁅g, a⁆`,
conjugation by `a' ∈ A` gives `⁅a'ga'⁻¹, a'aa'⁻¹⁆` (via
`conjugate_commutatorElement`), and `a'aa'⁻¹ ∈ A`. The multiplicative
and inverse closure cases reduce to a group-algebra rearrangement.
The backward direction of `mem_normalizer_iff` is obtained by applying
the forward helper with `a'⁻¹ ∈ A`.

(Was Increment 11's second "extras" axiom; discharged at Inc 21.) -/
theorem commg_normr
    {G : Type*} [Group G]
    (A : Subgroup G) :
    A ≤ Subgroup.normalizer
      ((⁅(⊤ : Subgroup G), A⁆ : Subgroup G) : Set G) := by
  -- Helper: conjugation by an element of A maps `⁅⊤, A⁆` into itself.
  have conj_into : ∀ (a' : G), a' ∈ A → ∀ g ∈ (⁅(⊤ : Subgroup G), A⁆ : Subgroup G),
      a' * g * a'⁻¹ ∈ (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) := by
    intro a' ha' g hg
    rw [Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨g₁, _hg₁, g₂, hg₂, rfl⟩ := hy
      rw [conjugate_commutatorElement]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (A.mul_mem (A.mul_mem ha' hg₂) (A.inv_mem ha'))
    | one => simp
    | mul x y _hx _hy ihx ihy =>
      have heq : a' * (x * y) * a'⁻¹ = (a' * x * a'⁻¹) * (a' * y * a'⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _hx ihx =>
      have heq : a' * x⁻¹ * a'⁻¹ = (a' * x * a'⁻¹)⁻¹ := by group
      rw [heq]
      exact Subgroup.inv_mem _ ihx
  intro a' ha'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_into a' ha' h hh, fun hh => ?_⟩
  have key : a'⁻¹ * (a' * h * a'⁻¹) * (a'⁻¹)⁻¹
           ∈ (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) :=
    conj_into a'⁻¹ (A.inv_mem ha') _ hh
  have eq : a'⁻¹ * (a' * h * a'⁻¹) * (a'⁻¹)⁻¹ = h := by group
  rw [eq] at key
  exact key

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

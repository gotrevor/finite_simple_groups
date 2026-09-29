/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

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
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

namespace FeitThompson.CommutatorExtras

open scoped commutatorElement

variable {G : Type*} [Group G]

/-
## DELETED AXIOM — `commutator_sup_le` (was the analog of MathComp `commMG`)

This file previously axiomatized, for subgroups `H`, `K`, `L` with `L`
normalizing both `H` and `K`:
  `⁅H ⊔ K, L⁆ ≤ ⁅H, L⁆ ⊔ ⁅K, L⁆`.

**That two-hypothesis statement is FALSE** (settled 2026-05-28 by exhaustive
small-group search). Counterexample in `S₄`:
  `H = ⟨(0 3 2 1)⟩ ≅ C₄`,  `K = ⟨(0 3)⟩`,  `L = ⟨(0 3)(1 2)⟩`.
Here `L ≤ N(H)` and `L ≤ N(K)` both hold, yet
  `⁅H ⊔ K, L⁆ = V₄` (order 4)  ⊄  `⁅H, L⁆ ⊔ ⁅K, L⁆` (order 2).
The hypotheses `L ≤ N(H)`, `L ≤ N(K)` do not control the cross-normalization
`K ≤ N(⁅H, L⁆)`, which fails in the counterexample.

The axiom's only consumer, `BGsection1/P1_6.lean` (`coprime_commGid`), is now
discharged honestly via the **proven** `commutator_sup_le_of_normalizers`
below. At that call site all four normalization clauses genuinely hold:
the two "self" clauses are `commutator_le_normalizer_left` (unconditional —
see above; the earlier "reduces to `A ⊴ G`" claim was a mistaken proof
attempt, not a real obstruction), the `K`-side cross clause is
`centralizer_le_normalizer_commutator_top` composed with
`centralizer_inf_normalizer_le_normalizer_commutator`, and the
`⁅K, L⁆ = ⁅C_G(A), A⁆ = ⊥` clause is `N(⊥) = ⊤`.

MathComp source for the (correctly-hypothesized) original:
`math-comp/solvable/commutator.v:236` (`commMG`), which carries the extra
`H ⊆ N([G, K])` hypothesis this axiom dropped.
-/

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

/-- An element that **centralizes `A`** and **normalizes `B`** also
normalizes `⁅B, A⁆`.

For `c ∈ C_G(A) ∩ N(B)`, conjugation sends a generator `⁅b, a⁆` to
`⁅cbc⁻¹, cac⁻¹⁆ = ⁅cbc⁻¹, a⁆` (since `c` centralizes `A`, `cac⁻¹ = a`),
and `cbc⁻¹ ∈ B` because `c` normalizes `B` — so the image is again a
generator of `⁅B, A⁆`. Closure induction extends this from generators to
all of `⁅B, A⁆`.

This is the general brick behind the asymmetric MathComp `commMG`
normalization side condition (`K ≤ N(⁅H, L⁆)`). The proof structure
mirrors `commg_normr`; only the `mem` case differs — `c` centralizing
`A` collapses `cac⁻¹` to `a`, and `c` normalizing `B` keeps `cbc⁻¹`
inside `B`. -/
theorem centralizer_inf_normalizer_le_normalizer_commutator
    {G : Type*} [Group G]
    (A B : Subgroup G) :
    Subgroup.centralizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((⁅B, A⁆ : Subgroup G) : Set G) := by
  have conj_into : ∀ (c : G), c ∈ Subgroup.centralizer (A : Set G) →
      c ∈ Subgroup.normalizer (B : Set G) →
      ∀ g ∈ (⁅B, A⁆ : Subgroup G),
      c * g * c⁻¹ ∈ (⁅B, A⁆ : Subgroup G) := by
    intro c hcA hcB g hg
    rw [Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, a, ha, rfl⟩ := hy
      rw [conjugate_commutatorElement]
      -- c * a * c⁻¹ = a since c centralizes A and a ∈ A.
      have hcomm : a * c = c * a := (Subgroup.mem_centralizer_iff.mp hcA) a ha
      have hfixA : c * a * c⁻¹ = a := by rw [← hcomm]; group
      -- c * b * c⁻¹ ∈ B since c normalizes B and b ∈ B.
      have hfixB : c * b * c⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hcB b).mp hb
      rw [hfixA]
      exact Subgroup.commutator_mem_commutator hfixB ha
    | one => simp
    | mul x y _hx _hy ihx ihy =>
      have heq : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _hx ihx =>
      have heq : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [heq]
      exact Subgroup.inv_mem _ ihx
  intro c hc
  obtain ⟨hcA, hcB⟩ := hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_into c hcA hcB h hh, fun hh => ?_⟩
  have hcB' : c⁻¹ ∈ Subgroup.normalizer (B : Set G) := Subgroup.inv_mem _ hcB
  have key : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ ∈ (⁅B, A⁆ : Subgroup G) :=
    conj_into c⁻¹ (Subgroup.inv_mem _ hcA) hcB' _ hh
  have eq : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ = h := by group
  rw [eq] at key
  exact key

/-- An element centralizing `A` normalizes `⁅⊤, A⁆` (the `B = ⊤`
specialization of `centralizer_inf_normalizer_le_normalizer_commutator`;
`N(⊤) = ⊤`, so the normalize-`B` condition is free).

Strengthens `commg_normr` from `A` to `C_G(A)`. This is exactly the
`K ≤ N(⁅H, L⁆)` side condition the asymmetric MathComp `commMG` needs at
the `commutator_sup_le` call site in `BGsection1/P1_6.lean` (with
`H = ⊤`, `L = A`). -/
theorem centralizer_le_normalizer_commutator_top
    {G : Type*} [Group G]
    (A : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer
      ((⁅(⊤ : Subgroup G), A⁆ : Subgroup G) : Set G) := by
  have h := centralizer_inf_normalizer_le_normalizer_commutator A (⊤ : Subgroup G)
  rwa [Subgroup.normalizer_eq_top, inf_top_eq] at h

/-- **The first argument normalizes the commutator subgroup.**

`H ≤ N(⁅H, L⁆)` for arbitrary subgroups `H, L` — equivalently, `⁅H, L⁆` is
normalized by `H` (and, symmetrically, by `L`), so `⁅H, L⁆ ⊴ ⟨H, L⟩`.

This is the **unconditional** "self-normalization" fact. An earlier analysis
(in the now-deleted `commutator_sup_le` axiom's docstring) mistakenly concluded
it "reduces to `H ≤ N(L)`" and is therefore false in general. That was an
artifact of attempting the proof by naive single-generator conjugation
`ʰ'⁅h,l⁆ = ⁅ʰ'h, ʰ'l⁆`, where `ʰ'l ∉ L`. The honest proof uses the Hall
identity (mathlib convention `⁅a,b⁆ = a·b·a⁻¹·b⁻¹`), which gives

  `h' · ⁅h, l⁆ · h'⁻¹ = ⁅h'·h, l⁆ · ⁅h', l⁆⁻¹`,

expressing the conjugate as a product of commutators whose *first* arguments
(`h'·h` and `h'`) stay in `H` — so it lands in `⁅H, L⁆` with no side
condition. (Verified empirically across S₃…A₅: `H ≤ N(⁅H,L⁆)` and
`L ≤ N(⁅H,L⁆)` hold for every subgroup pair, 0 counterexamples.) -/
theorem commutator_le_normalizer_left
    {G : Type*} [Group G]
    (H L : Subgroup G) :
    H ≤ Subgroup.normalizer ((⁅H, L⁆ : Subgroup G) : Set G) := by
  have conj_into : ∀ (h' : G), h' ∈ H → ∀ g ∈ (⁅H, L⁆ : Subgroup G),
      h' * g * h'⁻¹ ∈ (⁅H, L⁆ : Subgroup G) := by
    intro h' hh' g hg
    rw [Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, l, hl, rfl⟩ := hy
      -- Hall identity (mathlib convention ⁅a,b⁆ = a·b·a⁻¹·b⁻¹):
      --   h' ⁅a,l⁆ h'⁻¹ = ⁅h'·a, l⁆ · ⁅h', l⁆⁻¹.
      have hid : h' * ⁅a, l⁆ * h'⁻¹ = ⁅h' * a, l⁆ * ⁅h', l⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [hid]
      exact Subgroup.mul_mem _
        (Subgroup.commutator_mem_commutator (H.mul_mem hh' ha) hl)
        (Subgroup.inv_mem _
          (Subgroup.commutator_mem_commutator hh' hl))
    | one => simp
    | mul x y _hx _hy ihx ihy =>
      have heq : h' * (x * y) * h'⁻¹ = (h' * x * h'⁻¹) * (h' * y * h'⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _hx ihx =>
      have heq : h' * x⁻¹ * h'⁻¹ = (h' * x * h'⁻¹)⁻¹ := by group
      rw [heq]
      exact Subgroup.inv_mem _ ihx
  intro h' hh'
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_into h' hh' z hz, fun hz => ?_⟩
  have key : h'⁻¹ * (h' * z * h'⁻¹) * (h'⁻¹)⁻¹ ∈ (⁅H, L⁆ : Subgroup G) :=
    conj_into h'⁻¹ (H.inv_mem hh') _ hz
  have eq : h'⁻¹ * (h' * z * h'⁻¹) * (h'⁻¹)⁻¹ = z := by group
  rwa [eq] at key

/-- **Sup-distribution of the commutator (four-normalizer version).**

`⁅H ⊔ K, L⁆ ≤ ⁅H, L⁆ ⊔ ⁅K, L⁆`, provided all four of `H`, `K`
normalize both `⁅H, L⁆` and `⁅K, L⁆`.

This is the **provable form** of the (now-deleted, FALSE) `commutator_sup_le`
axiom. That axiom's two hypotheses (`L ≤ N(H)`, `L ≤ N(K)`) are NOT enough:
the closure-induction multiplication case conjugates `⁅y, l⁆` by an arbitrary
element `x ∈ H ⊔ K`, which forces
`H ⊔ K ≤ N(⁅H, L⁆ ⊔ ⁅K, L⁆)` — i.e. all four normalization clauses.
The two "self" clauses `H ≤ N(⁅H, L⁆)` and `K ≤ N(⁅K, L⁆)` are in fact
unconditionally true (`commutator_le_normalizer_left`); the two **cross**
clauses `H ≤ N(⁅K, L⁆)`, `K ≤ N(⁅H, L⁆)` are the genuine content and do
not follow from `L ≤ N(H)`/`L ≤ N(K)` alone. All four are taken as
hypotheses here to keep the lemma maximally reusable.

Proof: `H ⊔ K ≤ N(T)` (T := the RHS) from the four clauses via
`normalizer_inf_normalizer_le_normalizer_sup`; then `commutator_le` +
`closure_induction` on `H ⊔ K = closure (↑H ∪ ↑K)`. The `mul`/`inv`
cases use that the inductee lies in `H ⊔ K ≤ N(T)`, so conjugating an
element of `T` stays in `T`. -/
theorem commutator_sup_le_of_normalizers
    {G : Type*} [Group G]
    (H K L : Subgroup G)
    (hHH : H ≤ Subgroup.normalizer ((⁅H, L⁆ : Subgroup G) : Set G))
    (hHK : H ≤ Subgroup.normalizer ((⁅K, L⁆ : Subgroup G) : Set G))
    (hKH : K ≤ Subgroup.normalizer ((⁅H, L⁆ : Subgroup G) : Set G))
    (hKK : K ≤ Subgroup.normalizer ((⁅K, L⁆ : Subgroup G) : Set G)) :
    ⁅H ⊔ K, L⁆ ≤ ⁅H, L⁆ ⊔ ⁅K, L⁆ := by
  set T : Subgroup G := ⁅H, L⁆ ⊔ ⁅K, L⁆ with hT
  -- Step A: H ⊔ K normalizes T.
  have hsupN : Subgroup.normalizer ((⁅H, L⁆ : Subgroup G) : Set G) ⊓
      Subgroup.normalizer ((⁅K, L⁆ : Subgroup G) : Set G) ≤
        Subgroup.normalizer (T : Set G) :=
    Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _
  have hHN : H ≤ Subgroup.normalizer (T : Set G) :=
    fun x hx => hsupN ⟨hHH hx, hHK hx⟩
  have hKN : K ≤ Subgroup.normalizer (T : Set G) :=
    fun x hx => hsupN ⟨hKH hx, hKK hx⟩
  have hMN : H ⊔ K ≤ Subgroup.normalizer (T : Set G) := sup_le hHN hKN
  -- conjugation by a normalizer element keeps T-membership.
  have conj_mem : ∀ x ∈ H ⊔ K, ∀ t ∈ T, x * t * x⁻¹ ∈ T := fun x hx t ht =>
    (Subgroup.mem_normalizer_iff.mp (hMN hx) t).mp ht
  -- Step B: reduce to generators, then closure-induct on H ⊔ K.
  rw [Subgroup.commutator_le]
  intro x hx l hl
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hyH | hyK
    · exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hyH hl)
    · exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hyK hl)
  | one => rw [commutatorElement_one_left]; exact T.one_mem
  | mul a b ha hb iha ihb =>
    -- ⁅a*b, l⁆ = (a * ⁅b,l⁆ * a⁻¹) * ⁅a,l⁆
    have haHK : a ∈ H ⊔ K := by rwa [Subgroup.sup_eq_closure]
    have hsplit : ⁅a * b, l⁆ = (a * ⁅b, l⁆ * a⁻¹) * ⁅a, l⁆ := by
      simp only [commutatorElement_def]; group
    rw [hsplit]
    exact Subgroup.mul_mem _ (conj_mem a haHK _ ihb) iha
  | inv a ha iha =>
    -- ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a,l⁆⁻¹ * a
    have haHK : a ∈ H ⊔ K := by rwa [Subgroup.sup_eq_closure]
    have hainv : a⁻¹ ∈ H ⊔ K := Subgroup.inv_mem _ haHK
    have hsplit : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * (a⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hsplit]
    exact conj_mem a⁻¹ hainv _ (Subgroup.inv_mem _ iha)

end FeitThompson.CommutatorExtras

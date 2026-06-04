import Mathlib

/-!
# Perfectness of `SL(n, F)` for `n ≥ 3` — toward `PSL_isSimpleGroup_rank_ge_three`

The next deep axiom after `PSL(2,q)` is `PSL_isSimpleGroup_rank_ge_three`
(`LieType.lean`), whose Iwasawa route needs `commutator (SL n F) = ⊤`. Unlike the
`n = 2` case (`SL2.SL2_perfect`, which needed `|F| ≥ 4` via a diagonal-conjugation
trick), for `n ≥ 3` **every** elementary transvection is a commutator of
transvections — the Steinberg/Chevalley relation `⁅t_{ik}(a), t_{kj}(b)⁆ =
t_{ij}(ab)` using a third index `k` — with **no field-size restriction**.

This file machine-checks:

* `steinberg_comm` : the matrix-level Steinberg relation (axiom-clean, pure
  `Matrix.single` algebra). mathlib v4.29.1 lacks it.
* `transvecSL_mem_commutator` : for `3 ≤ |n|`, each `transvecSL` lies in
  `commutator (SL n F)`.
* `commutator_SLn_eq_top` : `commutator (SL n F) = ⊤` for `3 ≤ |n|`, **modulo**
  the generation fact `transvecSL_closure_eq_top` (transvections generate `SL n F`).

The sole remaining input is `transvecSL_closure_eq_top` — a disclosed `axiom`
here, currently out at Aristotle. mathlib has `Matrix.diagonal_transvection_induction`
(every matrix is a product of diagonals + transvections) and the Gaussian-reduction
machinery; the missing step is that a det-1 diagonal is a product of transvections
(Whitehead/Steinberg). Once it lands, this file's perfectness becomes axiom-clean.
-/

open Matrix
open scoped commutatorElement

namespace FiniteSimpleGroups.SLn

variable {n : Type*} [DecidableEq n] [Fintype n] {F : Type*} [Field F]

/-- **Steinberg/Chevalley commutator relation** for elementary transvections in
type `A`: for pairwise-distinct `i, j, k`, `⁅t_{ik}(a), t_{kj}(b)⁆ = t_{ij}(a·b)`
written with explicit inverses (`t_{ik}(a)⁻¹ = t_{ik}(-a)`). Pure matrix identity. -/
theorem steinberg_comm {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (a b : F) :
    transvection i k a * transvection k j b * transvection i k (-a) * transvection k j (-b)
      = transvection i j (a * b) := by
  have hki : k ≠ i := hik.symm
  have hjk : j ≠ k := hkj.symm
  have hji : j ≠ i := hij.symm
  have sneg : ∀ (x y : n) (c : F), single x y (-c) = -single x y c := fun x y c => by
    rw [eq_neg_iff_add_eq_zero, ← single_add, neg_add_cancel, single_zero]
  have v1 : ∀ x y : F, single i k x * single i k y = (0 : Matrix n n F) :=
    fun x y => by rw [single_mul_single_of_ne (h := hki)]
  have v2 : ∀ x y : F, single k j x * single i k y = (0 : Matrix n n F) :=
    fun x y => by rw [single_mul_single_of_ne (h := hji)]
  have v3 : ∀ x y : F, single k j x * single k j y = (0 : Matrix n n F) :=
    fun x y => by rw [single_mul_single_of_ne (h := hjk)]
  have v4 : ∀ x y : F, single i k x * single i j y = (0 : Matrix n n F) :=
    fun x y => by rw [single_mul_single_of_ne (h := hki)]
  have v5 : ∀ x y : F, single k j x * single i j y = (0 : Matrix n n F) :=
    fun x y => by rw [single_mul_single_of_ne (h := hji)]
  simp only [transvection, sneg]
  noncomm_ring
  simp only [single_mul_single_same, v1, v2, v3, v4, v5, mul_zero, zero_mul, smul_zero]
  abel

/-- The transvection `transvection i j c` as an element of `SL(n,F)` (det = 1). -/
def transvecSL {i j : n} (h : i ≠ j) (c : F) : SpecialLinearGroup n F :=
  ⟨transvection i j c, det_transvection_of_ne i j h c⟩

@[simp] lemma transvecSL_val {i j : n} (h : i ≠ j) (c : F) :
    (transvecSL h c).val = transvection i j c := rfl

/-- `t_{ij}(c)⁻¹ = t_{ij}(-c)` in `SL(n,F)`. -/
lemma transvecSL_inv {i j : n} (h : i ≠ j) (c : F) :
    (transvecSL h c)⁻¹ = transvecSL h (-c) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  show transvection i j c * transvection i j (-c) = (1 : Matrix n n F)
  rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero]

/-- **For `3 ≤ |n|`, every elementary transvection is a commutator in `SL(n,F)`.**
Pick a third index `k ≠ i, j`; then `⁅t_{ik}(c), t_{kj}(1)⁆ = t_{ij}(c)` by
`steinberg_comm`, and a commutator lies in `commutator (SL n F)`. No field-size
hypothesis (the `n = 2` obstruction disappears once a third coordinate exists). -/
theorem transvecSL_mem_commutator (h3 : 3 ≤ Fintype.card n) {i j : n} (hij : i ≠ j)
    (c : F) : transvecSL hij c ∈ commutator (SpecialLinearGroup n F) := by
  -- a third index distinct from i, j
  obtain ⟨k, hk⟩ : ∃ k : n, k ∉ ({i, j} : Finset n) := by
    have hcard : ({i, j} : Finset n).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have hne : ¬ (Finset.univ : Finset n) ⊆ ({i, j} : Finset n) := by
      intro hsub
      have := Finset.card_le_card hsub
      rw [Finset.card_univ] at this
      omega
    obtain ⟨k, _, hk⟩ := Finset.not_subset.mp hne
    exact ⟨k, hk⟩
  rw [Finset.mem_insert, Finset.mem_singleton] at hk
  push_neg at hk
  obtain ⟨hki, hkj⟩ := hk
  have hik : i ≠ k := fun h => hki h.symm
  have hjk : k ≠ j := fun h => hkj h
  -- the group commutator ⁅t_{ik}(c), t_{kj}(1)⁆ equals t_{ij}(c)
  have key : ⁅transvecSL hik c, transvecSL hjk (1 : F)⁆ = transvecSL hij c := by
    rw [commutatorElement_def, transvecSL_inv, transvecSL_inv]
    apply Subtype.ext
    show transvection i k c * transvection k j 1 * transvection i k (-c) * transvection k j (-1)
        = transvection i j c
    rw [steinberg_comm hij hik hjk c 1, mul_one]
  rw [← key]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **Transvections generate `SL(n,F)`** (over a field). DISCLOSED AXIOM (out at
Aristotle): every `g : SL n F` lies in the subgroup generated by the elementary
transvections `transvecSL`. mathlib has `diagonal_transvection_induction` (matrices
= products of diagonals + transvections) and the Gaussian-reduction machinery;
the missing piece is that a det-1 diagonal is a product of transvections
(Whitehead). For `n = 2` this is `SL2.transvections_generate` (proved). -/
axiom transvecSL_closure_eq_top :
    Subgroup.closure
      {g : SpecialLinearGroup n F | ∃ (i j : n) (h : i ≠ j) (c : F), g = transvecSL h c} = ⊤

/-- **`SL(n,F)` is perfect for `3 ≤ |n|`** — `commutator (SL n F) = ⊤`. Every
generating transvection is a commutator (`transvecSL_mem_commutator`), so the
generated subgroup `⊤` (`transvecSL_closure_eq_top`) is contained in the commutator
subgroup. Modulo the generation axiom; the Steinberg core is machine-checked. -/
theorem commutator_SLn_eq_top (h3 : 3 ≤ Fintype.card n) :
    commutator (SpecialLinearGroup n F) = ⊤ := by
  rw [eq_top_iff, ← transvecSL_closure_eq_top]
  rw [Subgroup.closure_le]
  rintro g ⟨i, j, h, c, rfl⟩
  exact transvecSL_mem_commutator h3 h c

/-- **`PSL(n,F)` is perfect for `3 ≤ |n|`** (modulo the generation axiom) — the
first Iwasawa obligation for `PSL(n,q)` simplicity, `n ≥ 3`. Perfectness descends
from `SL(n,F)` (`commutator_SLn_eq_top`) along the surjection onto the quotient by
its center (`PSL = SL/Z`), exactly as in the `n = 2` case (`SL2.PSL2_perfect`). -/
theorem commutator_PSLn_eq_top (h3 : 3 ≤ Fintype.card n) :
    commutator (SpecialLinearGroup n F ⧸
      Subgroup.center (SpecialLinearGroup n F)) = ⊤ := by
  set G := SpecialLinearGroup n F
  let f := QuotientGroup.mk' (Subgroup.center G)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hmap : commutator (G ⧸ Subgroup.center G) = Subgroup.map f (commutator G) := by
    show ⁅(⊤ : Subgroup _), ⊤⁆ = Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [hmap, commutator_SLn_eq_top h3, Subgroup.map_top_of_surjective f hf]

end FiniteSimpleGroups.SLn

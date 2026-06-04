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
* `transvecSL_closure_eq_top` : transvections generate `SL(n,F)` (the Whitehead
  reduction — det-1 diagonal = product of transvections via the five-transvection
  `diag(a,a⁻¹)` identity + strong induction). **Now machine-checked** (no longer an
  axiom); built on `Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`.
* `commutator_SLn_eq_top` : `commutator (SL n F) = ⊤` for `3 ≤ |n|`.

This file is now **axiom-clean** (only the standard `propext`/`Classical.choice`/
`Quot.sound`): the last disclosed input, `transvecSL_closure_eq_top`, was discharged.
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

section TransvecGenerate
open Finset Classical

private abbrev S : Set (SpecialLinearGroup n F) :=
  {g | ∃ (i j : n) (h : i ≠ j) (c : F), g = transvecSL h c}

/-- A `transvecSL` element belongs to the subgroup closure of transvections. -/
private lemma transvecSL_mem_closure {i j : n} (h : i ≠ j) (c : F) :
    transvecSL h c ∈ Subgroup.closure S :=
  Subgroup.subset_closure ⟨i, j, h, c, rfl⟩

/-- Product of a list of `TransvectionStruct` matrices has determinant 1. -/
private lemma det_list_transvec_prod (L : List (TransvectionStruct n F)) :
    (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons, det_mul, ih, mul_one, t.det]

/-
Lifting a list of `TransvectionStruct` matrices to `SL` gives an element of the closure.
-/
private lemma list_transvec_prod_mem_closure (L : List (TransvectionStruct n F)) :
    (⟨(L.map TransvectionStruct.toMatrix).prod, det_list_transvec_prod L⟩ :
      SpecialLinearGroup n F) ∈ Subgroup.closure S := by
  induction' L with t L ih;
  · exact OneMemClass.one_mem _;
  · convert Subgroup.mul_mem _ ( transvecSL_mem_closure t.hij t.c ) ih using 1

/-! ### Whitehead lemma: diagonal matrices with det 1 are products of transvections -/

/-- The "elementary diagonal" function: `a` at position `i`, `a⁻¹` at position `j`,
    and `1` elsewhere. -/
noncomputable def elemDiagFn (i j : n) (a : F) : n → F :=
  Function.update (Function.update (fun _ => (1 : F)) i a) j a⁻¹

/-
The 5-transvection identity: for `i ≠ j` and `a ≠ 0`,
    `E_{ij}(a) · E_{ji}(-a⁻¹) · E_{ij}(a-1) · E_{ji}(1) · E_{ij}(-1) = diag(a at i, a⁻¹ at j)`.
-/
/-- The intermediate matrix after the first 3 transvections in the Whitehead identity.
    Entries: 0 at (i,i), a at (i,j), -a⁻¹ at (j,i), a⁻¹ at (j,j), δ elsewhere. -/
private noncomputable def wIntermediateFn (i j : n) (a : F) (p q : n) : F :=
  if p = i ∧ q = j then a
  else if p = j ∧ q = i then -a⁻¹
  else if p = i ∧ q = i then 0
  else if p = j ∧ q = j then a⁻¹
  else if p = q then 1
  else 0

private lemma three_transvec_eq_intermediate (i j : n) (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    transvection i j a * transvection j i (-a⁻¹) * transvection i j (a - 1) =
    Matrix.of (wIntermediateFn i j a) := by
  ext p q; simp +decide [ *, Matrix.mul_apply, Matrix.of_apply ] ;
  simp +decide [ wIntermediateFn, Matrix.mul_apply, transvection ];
  simp +decide [ Matrix.one_apply, Matrix.single, Finset.sum_add_distrib, add_mul, mul_add, Finset.mul_sum, Finset.sum_mul ];
  rw [ Finset.sum_eq_single j, Finset.sum_eq_single i ] <;> simp +contextual [ *, eq_comm ];
  grind +ring

private lemma intermediate_mul_two_eq_diag (i j : n) (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    Matrix.of (wIntermediateFn i j a) * transvection j i 1 * transvection i j (-1) =
    diagonal (elemDiagFn i j a) := by
  ext p q; by_cases h : p = i <;> by_cases h' : q = j <;> simp +decide [ *, transvection, Matrix.mul_apply, Matrix.diagonal ] ;
  · simp +decide [ wIntermediateFn, Matrix.one_apply, Matrix.single, Finset.sum_add_distrib, add_mul, mul_add, Finset.mul_sum, Finset.sum_mul ];
    aesop;
  · simp +decide [ wIntermediateFn, Matrix.one_apply, Matrix.single, Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, ha, hij, h, h' ];
    by_cases hi : i = q <;> simp +decide [ hi, hij, h' ];
    · simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, hij, h', hi, elemDiagFn ];
      rw [ Finset.sum_eq_zero ] ; aesop;
    · rw [ Finset.sum_eq_zero ] ; aesop;
  · simp +decide [ Matrix.one_apply, Matrix.single, Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul, wIntermediateFn, elemDiagFn ];
    aesop;
  · simp +decide [ *, Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Matrix.one_apply, Matrix.single, wIntermediateFn, elemDiagFn ];
    by_cases h'' : j = q <;> by_cases h''' : i = q <;> simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
    · split_ifs <;> ring;
    · aesop

set_option maxHeartbeats 400000 in
private lemma five_transvec_eq_elem_diag (i j : n) (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    transvection i j a * transvection j i (-a⁻¹) * transvection i j (a - 1) *
    transvection j i 1 * transvection i j (-1) = diagonal (elemDiagFn i j a) := by
  rw [show transvection i j a * transvection j i (-a⁻¹) * transvection i j (a - 1) *
    transvection j i 1 * transvection i j (-1) =
    (transvection i j a * transvection j i (-a⁻¹) * transvection i j (a - 1)) *
    transvection j i 1 * transvection i j (-1) from by ring]
  rw [three_transvec_eq_intermediate i j hij a ha]
  exact intermediate_mul_two_eq_diag i j hij a ha

/-
The determinant of an elementary diagonal function is 1.
-/
private lemma det_elemDiag (i j : n) (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    (diagonal (elemDiagFn i j a)).det = 1 := by
  have hi : elemDiagFn i j a i = a := by simp [elemDiagFn, Function.update_apply, hij]
  have hj : elemDiagFn i j a j = a⁻¹ := by simp [elemDiagFn, Function.update_apply]
  rw [Matrix.det_diagonal,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (elemDiagFn i j a)
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
    hi, hj, Finset.prod_eq_one, mul_one, mul_inv_cancel₀ ha]
  intro k hk
  obtain ⟨hkj, hk'⟩ := Finset.mem_erase.mp hk
  have hki := (Finset.mem_erase.mp hk').1
  simp [elemDiagFn, Function.update_apply, hkj, hki]

/-
An elementary diagonal matrix lies in the transvection closure.
-/
private lemma elem_diag_mem_closure (i j : n) (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    (⟨diagonal (elemDiagFn i j a), det_elemDiag i j hij a ha⟩ :
      SpecialLinearGroup n F) ∈ Subgroup.closure S := by
  convert Subgroup.mul_mem _ ( Subgroup.mul_mem _ ( Subgroup.mul_mem _ ( Subgroup.mul_mem _ ( transvecSL_mem_closure hij a ) ( transvecSL_mem_closure ( Ne.symm hij ) ( -a⁻¹ ) ) ) ( transvecSL_mem_closure hij ( a - 1 ) ) ) ( transvecSL_mem_closure ( Ne.symm hij ) 1 ) ) ( transvecSL_mem_closure hij ( -1 ) ) using 1;
  ext; simp [transvecSL];
  rw [ ← five_transvec_eq_elem_diag i j hij a ha ]

/-
If all entries of `D` are 1, then `diagonal D` is the identity.
-/
omit [Fintype n] in
private lemma diag_all_one (D : n → F) (hD : ∀ i, D i = 1) :
    diagonal D = (1 : Matrix n n F) := by
  ext i j; by_cases hij : i = j <;> simp +decide [ hD, hij ] ;
  simp +decide [ hij, Matrix.one_apply ]

/-
Key factorization: `diagonal D = diagonal (elemDiagFn i j (D i)) * diagonal D'`
    where `D' i = 1` and `D' j = D i * D j`.
-/
private lemma diag_factor (D : n → F) (i j : n) (hij : i ≠ j) (hi : D i ≠ 0) :
    diagonal D = diagonal (elemDiagFn i j (D i)) *
      diagonal (Function.update (Function.update D i 1) j (D i * D j)) := by
  ext k l; by_cases hk : k = l <;> simp_all +decide [ elemDiagFn ] ;
  by_cases hl : l = i <;> by_cases hl' : l = j <;> simp_all +decide [ Function.update_apply ]

/-
The number of non-1 entries decreases after factoring out an elementary diagonal.
-/
private lemma nonone_card_lt (D : n → F) (i j : n) (hij : i ≠ j)
    (hi : D i ≠ 1) (hj : D j ≠ 1) :
    (Finset.univ.filter fun k =>
      (Function.update (Function.update D i 1) j (D i * D j)) k ≠ 1).card <
    (Finset.univ.filter fun k => D k ≠ 1).card := by
  refine' Finset.card_lt_card _;
  simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
  grind

/-
If `∏ D i = 1` and some `D i₀ ≠ 1`, then there exists `j₀ ≠ i₀` with `D j₀ ≠ 1`.
-/
private lemma exists_ne_of_prod_one_ne_one (D : n → F) (hD : ∏ i, D i = 1)
    (i₀ : n) (hi₀ : D i₀ ≠ 1) : ∃ j₀, j₀ ≠ i₀ ∧ D j₀ ≠ 1 := by
  by_contra! h_contra;
  rw [ Finset.prod_eq_single i₀ ] at hD <;> aesop

/-
The determinant of the updated diagonal after factoring is still 1.
-/
private lemma det_update_factor (D : n → F) (i j : n) (hij : i ≠ j) (hD : ∏ k, D k = 1)
    (hi : D i ≠ 0) :
    ∏ k, (Function.update (Function.update D i 1) j (D i * D j)) k = 1 := by
  convert hD using 1;
  rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i ), ← Finset.prod_erase_mul _ _ ( Finset.mem_erase_of_ne_of_mem ( Ne.symm hij ) ( Finset.mem_univ j ) ) ];
  rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ i ), ← Finset.prod_erase_mul _ _ ( Finset.mem_erase_of_ne_of_mem ( Ne.symm hij ) ( Finset.mem_univ j ) ) ];
  simp +decide [ *, Function.update_apply ];
  rw [ Finset.prod_congr rfl fun x hx => by aesop ] ; ring

/-
**Whitehead lemma**: a diagonal matrix with determinant 1 lies in the transvection closure.
-/
private lemma diag_det_one_mem_closure (D : n → F) (hD : (diagonal D).det = 1) :
    (⟨diagonal D, hD⟩ : SpecialLinearGroup n F) ∈ Subgroup.closure S := by
  -- Use strong induction on k = (univ.filter (fun i => D i ≠ 1)).card.
  induction' k : (Finset.univ.filter (fun i => D i ≠ 1)).card using Nat.strong_induction_on with k ih generalizing D;
  by_cases h_all_one : ∀ i, D i = 1;
  · have h1 : diagonal D = 1 := diag_all_one D h_all_one
    revert hD; rw [h1]; intro hD
    convert Subgroup.one_mem (Subgroup.closure S)
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀, D i₀ ≠ 1 := by
      exact not_forall.mp h_all_one
    obtain ⟨j₀, hj₀_ne_i₀, hj₀⟩ : ∃ j₀, j₀ ≠ i₀ ∧ D j₀ ≠ 1 := by
      contrapose! h_all_one;
      simp_all +decide [ Finset.prod_eq_single i₀ ]
    set D' : n → F := Function.update (Function.update D i₀ 1) j₀ (D i₀ * D j₀)
    have hD' : (diagonal D).det = 1 := by
      exact hD
    have hD'_det : (diagonal D').det = 1 := by
      convert det_update_factor D i₀ j₀ ( Ne.symm hj₀_ne_i₀ ) _ _ using 1;
      · rw [ Matrix.det_diagonal ];
      · rwa [ Matrix.det_diagonal ] at hD';
      · intro h; simp_all +decide [ Matrix.det_diagonal ] ;
        exact absurd ( hD' ▸ Finset.prod_eq_zero ( Finset.mem_univ i₀ ) h ) ( by simp +decide )
    have h_card_lt : (Finset.univ.filter (fun i => D' i ≠ 1)).card < (Finset.univ.filter (fun i => D i ≠ 1)).card := by
      apply_rules [ nonone_card_lt ];
    have h_diag_factor : diagonal D = diagonal (elemDiagFn i₀ j₀ (D i₀)) * diagonal D' := by
      convert diag_factor D i₀ j₀ ( Ne.symm hj₀_ne_i₀ ) _ using 1;
      intro h; simp_all +decide [ Finset.prod_eq_zero ( Finset.mem_univ i₀ ) ] ;
    convert Subgroup.mul_mem _ ( elem_diag_mem_closure i₀ j₀ ( Ne.symm hj₀_ne_i₀ ) ( D i₀ ) ?_ ) ( ih _ ?_ D' hD'_det rfl ) using 1;
    refine Subtype.ext h_diag_factor;
    · intro h; simp_all +decide [ Finset.prod_eq_zero ( Finset.mem_univ i₀ ) ] ;
    · linarith

/-- **Transvections generate `SL(n,F)`** (over a field) — formerly a disclosed axiom,
now machine-checked. Proof (Whitehead reduction, verified in our kernel via a brick
auto-formalized by Aristotle and ported here): any `M : SL n F` factors as
`L.prod * diagonal D * L'.prod` with `L, L'` lists of transvections
(`Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`); the transvection products
lie in the closure, and a det-1 diagonal lies in the closure by strong induction on its
number of non-`1` entries, factoring off an "elementary diagonal" `diag(a,a⁻¹)` (a product
of five transvections) at each step. -/
theorem transvecSL_closure_eq_top :
    Subgroup.closure
      {g : SpecialLinearGroup n F | ∃ (i j : n) (h : i ≠ j) (c : F), g = transvecSL h c} = ⊤ := by
  refine' eq_top_iff.mpr _;
  intro A hA
  obtain ⟨L, L', D, h_eq⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (↑A : Matrix n n F);
  convert Subgroup.mul_mem _ ( Subgroup.mul_mem _ ( list_transvec_prod_mem_closure L ) ( diag_det_one_mem_closure D ?_ ) ) ( list_transvec_prod_mem_closure L' ) using 1;
  exact Subtype.ext h_eq;
  apply_fun Matrix.det at h_eq; simp_all +decide [ Matrix.det_mul ] ;

end TransvecGenerate

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

/-- **`PSL(n,F)` is nontrivial for `2 ≤ |n|`** — the Iwasawa `Nontrivial` obligation
for `PSL(n,q)` simplicity. A transvection `t_{ij}(1)` (`i ≠ j`) is not central — its
off-diagonal `(i,j)` entry is `1`, while every central element is a scalar matrix
(mathlib `SpecialLinearGroup.mem_center_iff`) — so its image in `SL/Z` is `≠ 1`.
Axiom-clean (independent of the generation axiom). -/
theorem PSLn_nontrivial (h2 : 2 ≤ Fintype.card n) :
    Nontrivial (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F)) := by
  have : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  refine ⟨QuotientGroup.mk (transvecSL hij 1), 1, ?_⟩
  rw [Ne, QuotientGroup.eq_one_iff]
  intro hmem
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem
  obtain ⟨r, hr, hscal⟩ := hmem
  have hentry := congr_fun₂ hscal i j
  rw [transvecSL_val] at hentry
  simp only [scalar_apply, diagonal_apply_ne _ hij, transvection, add_apply, one_apply_ne hij,
    single_apply_same, zero_add] at hentry
  exact one_ne_zero hentry.symm

end FiniteSimpleGroups.SLn

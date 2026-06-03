import Mathlib
import FiniteSimpleGroups.LieType

/-!
# `SL(2,F)` is perfect, and `PSL(2,q)` is perfect — the Iwasawa "perfect" obligation

`PSLIwasawa.lean` reduces `PSL_isSimpleGroup` for `PSL 2 q` (an `axiom` in
`LieType.lean`) to the five Iwasawa obligations. This file **discharges one of
them — perfectness** — from scratch and fully axiom-free:

* `SL2_perfect` : `commutator (SL(2,F)) = ⊤` for any field with `4 ≤ |F|`.
* `PSL2_perfect` : `commutator (PSL 2 q) = ⊤` for `q` prime with `4 ≤ q`
  (the Iwasawa "perfect" obligation).
* `PSL2_nontrivial` : `Nontrivial (PSL 2 q)` for every prime `q`
  (the Iwasawa `Nontrivial` obligation).

Two of the five Iwasawa obligations of `PSL2_isSimpleGroup_of_iwasawa` are thus
machine-checked here; the remaining three (the projective-line action,
quasi-preprimitivity, the Iwasawa structure of unipotent subgroups) await the
`ℙ¹(F_q)` action construction.

Mathlib v4.29.1 has `PSL`/`SL` and the transvection machinery but **no** SL(2)
perfectness and **no** PSL simplicity, so this is genuine new content, consistent
with the repository's "one rule" (never re-derive what mathlib already has).

## Proof outline

The two elementary transvection families `upper t = !![1,t;0,1]` and
`lower t = !![1,0;t,1]` generate `SL(2,F)` (`transvections_generate`, via the
direct Bruhat decomposition for `2×2` matrices and the Steinberg identity
`diagSL_eq` writing `diag(a,a⁻¹)` as a product of transvections). Each
transvection is a commutator: the diagonal-conjugation identity
`⁅diag(a,a⁻¹), upper s⁆ = upper((a²−1)s)` (`comm_diag_upper`, and the `lower`
analogue) makes `s ↦ (a²−1)s` surjective once `a² ≠ 1`, which holds for some
`a ≠ 0` when `|F| ≥ 4` (`exists_sq_ne_one`). Hence the commutator subgroup
contains a generating set, so it is `⊤`. Perfectness then descends to the
quotient `PSL(2,q) = SL(2,q)/Z` (`perfect_of_surjective`).
-/

namespace FiniteSimpleGroups
namespace SL2

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F] [DecidableEq F]

/-- The upper elementary transvection `!![1, t; 0, 1]` in `SL(2,F)`. -/
def upper (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower elementary transvection `!![1, 0; t, 1]` in `SL(2,F)`. -/
def lower (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem upper_val (t : F) : (upper t).val = !![1, t; 0, 1] := rfl
@[simp] theorem lower_val (t : F) : (lower t).val = !![1, 0; t, 1] := rfl

/-- The diagonal `SL₂` element `diag(a, a⁻¹)`. -/
def diagSL (a : F) (ha : a ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, mul_inv_cancel₀ ha]⟩

@[simp] theorem diagSL_val (a : F) (ha : a ≠ 0) : (diagSL a ha).val = !![a, 0; 0, a⁻¹] := rfl

/-- **Steinberg diagonal identity:** `diag(a,a⁻¹)` is a product of transvections. -/
theorem diagSL_eq (a : F) (ha : a ≠ 0) :
    diagSL a ha =
      upper a * lower (-a⁻¹) * upper a * upper (-1) * lower 1 * upper (-1) := by
  apply Subtype.ext
  simp only [diagSL, SpecialLinearGroup.coe_mul, upper_val, lower_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The generating set: upper and lower transvections. -/
def S : Set (SpecialLinearGroup (Fin 2) F) :=
  Set.range (upper (F := F)) ∪ Set.range (lower (F := F))

theorem upper_mem_closure (t : F) : upper t ∈ Subgroup.closure (S (F := F)) :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

theorem lower_mem_closure (t : F) : lower t ∈ Subgroup.closure (S (F := F)) :=
  Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)

theorem diagSL_mem_closure (a : F) (ha : a ≠ 0) :
    diagSL a ha ∈ Subgroup.closure (S (F := F)) := by
  rw [diagSL_eq a ha]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (upper_mem_closure a) (lower_mem_closure _)) (upper_mem_closure a))
    (upper_mem_closure _)) (lower_mem_closure 1)) (upper_mem_closure _)

/-- Bruhat decomposition, `c ≠ 0`: `!![a,b;c,d] = upper((a-1)/c)·lower c·upper((d-1)/c)`. -/
theorem mk_eq_c_ne (a b c d : F) (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    (h : (!![a, b; c, d]).det = 1) :
    (⟨!![a, b; c, d], h⟩ : SpecialLinearGroup (Fin 2) F)
      = upper ((a - 1) / c) * lower c * upper ((d - 1) / c) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, upper_val, lower_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring) <;>
    (try linear_combination hdet) <;> (try linear_combination -hdet)

/-- Bruhat decomposition, `c = 0`: `!![a,b;0,d] = diag(a,a⁻¹)·upper(b·a⁻¹)`. -/
theorem mk_eq_c_eq (a b d : F) (hdet : a * d - b * 0 = 1)
    (h : (!![a, b; 0, d]).det = 1) :
    ∃ ha : a ≠ 0,
      (⟨!![a, b; 0, d], h⟩ : SpecialLinearGroup (Fin 2) F) = diagSL a ha * upper (b * a⁻¹) := by
  rw [mul_zero, sub_zero] at hdet
  have ha : a ≠ 0 := by rintro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  refine ⟨ha, ?_⟩
  apply Subtype.ext
  simp only [diagSL, SpecialLinearGroup.coe_mul, upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring) <;>
    (try linear_combination hdet) <;> (try linear_combination -hdet)

/-- **The elementary transvections generate `SL(2,F)`.** -/
theorem transvections_generate :
    Subgroup.closure (S (F := F)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  induction g using SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
    by_cases hc : c = 0
    · subst hc
      obtain ⟨ha, hg⟩ := mk_eq_c_eq a b d hdet _
      rw [hg]
      exact mul_mem (diagSL_mem_closure a ha) (upper_mem_closure _)
    · rw [mk_eq_c_ne a b c d hdet hc _]
      exact mul_mem (mul_mem (upper_mem_closure _) (lower_mem_closure _)) (upper_mem_closure _)

/-! ### Commutator identities and perfectness -/

@[simp] theorem upper_mul (s t : F) : upper s * upper t = upper (s + t) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, upper_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;> ring

theorem upper_inv (s : F) : (upper s)⁻¹ = upper (-s) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, upper_val, SpecialLinearGroup.coe_one,
      Matrix.mul_fin_two, Fin.sum_univ_two, Matrix.one_fin_two] <;> ring

theorem lower_inv (s : F) : (lower s)⁻¹ = lower (-s) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, lower_val, SpecialLinearGroup.coe_one,
      Matrix.mul_fin_two, Fin.sum_univ_two, Matrix.one_fin_two] <;> ring

theorem diagSL_inv (a : F) (ha : a ≠ 0) :
    (diagSL a ha)⁻¹ = diagSL a⁻¹ (inv_ne_zero ha) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, diagSL_val, SpecialLinearGroup.coe_one,
      Matrix.mul_fin_two, Fin.sum_univ_two, Matrix.one_fin_two] <;>
    (try field_simp)

/-- `⁅diag(a,a⁻¹), upper s⁆ = upper((a²-1)·s)`. -/
theorem comm_diag_upper (a : F) (ha : a ≠ 0) (s : F) :
    ⁅diagSL a ha, upper s⁆ = upper ((a ^ 2 - 1) * s) := by
  rw [commutatorElement_def, upper_inv, diagSL_inv a ha]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, diagSL_val, upper_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> ring

/-- `⁅diag(a,a⁻¹), lower s⁆ = lower((a⁻²-1)·s)`. -/
theorem comm_diag_lower (a : F) (ha : a ≠ 0) (s : F) :
    ⁅diagSL a ha, lower s⁆ = lower ((a⁻¹ ^ 2 - 1) * s) := by
  rw [commutatorElement_def, lower_inv, diagSL_inv a ha]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, diagSL_val, lower_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> ring

/-- For a field with `4 ≤ |F|`, some `a` has `a ≠ 0` and `a² ≠ 1`. -/
theorem exists_sq_ne_one [Fintype F] (hF : 4 ≤ Fintype.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h1 : a ^ 2 = 1 := h a ha
      have : a = 1 ∨ a = -1 := by rw [sq] at h1; exact mul_self_eq_one_iff.mp h1
      rcases this with h2 | h2 <;> simp [h2]
  have hcard : Fintype.card F ≤ 3 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    refine this.trans ?_
    calc ({0, 1, -1} : Finset F).card
        ≤ ({1, -1} : Finset F).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({-1} : Finset F).card + 1) + 1 := by gcongr; exact Finset.card_insert_le _ _
      _ ≤ 3 := by simp
  omega

/-- **`SL(2,F)` is perfect when `4 ≤ |F|`.** -/
theorem SL2_perfect [Fintype F] (hF : 4 ≤ Fintype.card F) :
    commutator (SpecialLinearGroup (Fin 2) F) = ⊤ := by
  obtain ⟨a, ha, ha2⟩ := exists_sq_ne_one hF
  have hunit : a ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ha2
  have hunit' : a⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [sub_ne_zero, inv_pow, ne_eq, inv_eq_one]; exact ha2
  have hupper : ∀ t : F, upper t ∈ commutator (SpecialLinearGroup (Fin 2) F) := by
    intro t
    have key : upper t = ⁅diagSL a ha, upper ((a ^ 2 - 1)⁻¹ * t)⁆ := by
      rw [comm_diag_upper a ha]; congr 1
      rw [← mul_assoc, mul_inv_cancel₀ hunit, one_mul]
    rw [key]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hlower : ∀ t : F, lower t ∈ commutator (SpecialLinearGroup (Fin 2) F) := by
    intro t
    have key : lower t = ⁅diagSL a ha, lower ((a⁻¹ ^ 2 - 1)⁻¹ * t)⁆ := by
      rw [comm_diag_lower a ha]; congr 1
      rw [← mul_assoc, mul_inv_cancel₀ hunit', one_mul]
    rw [key]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [eq_top_iff, ← transvections_generate, Subgroup.closure_le]
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact hupper t
  · exact hlower t

/-- Perfectness descends along a surjective group homomorphism. -/
theorem perfect_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (h : commutator G = ⊤) : commutator H = ⊤ := by
  have hmap : commutator H = Subgroup.map f (commutator G) := by
    show ⁅(⊤ : Subgroup H), ⊤⁆ = Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [hmap, h, Subgroup.map_top_of_surjective f hf]

/-- **`PSL(2,q)` is perfect** for `q` prime with `4 ≤ q` — the Iwasawa
"perfect" obligation for `PSL_isSimpleGroup` at `n = 2`. -/
theorem PSL2_perfect (q : ℕ) [Fact (Nat.Prime q)] (hq : 4 ≤ q) :
    commutator (PSL 2 q) = ⊤ := by
  have hcard : 4 ≤ Fintype.card (ZMod q) := by rw [ZMod.card]; exact hq
  exact perfect_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (SL2_perfect hcard)

/-! ### Nontriviality of `PSL(2,q)` -/

/-- `upper 1` is not central in `SL(2,F)`: it fails to commute with `lower 1`
(their products differ in the `(0,0)` entry, `1 ≠ 2` in any field). -/
theorem upper_one_notMem_center (F : Type*) [Field F] [DecidableEq F] :
    upper (1 : F) ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [Subgroup.mem_center_iff]
  push_neg
  refine ⟨lower 1, ?_⟩
  intro heq
  have h00 : (lower (1 : F) * upper 1).val 0 0 = (upper (1 : F) * lower 1).val 0 0 := by
    rw [heq]
  simp [upper_val, lower_val] at h00

/-- **`PSL(2,q)` is nontrivial** for every prime `q` — the Iwasawa
`Nontrivial` obligation for `PSL_isSimpleGroup` at `n = 2`. (Holds for all
primes, including the non-simple `q = 2, 3`: `SL(2,q)` is always non-abelian,
so its quotient by the center is nontrivial.) -/
theorem PSL2_nontrivial (q : ℕ) [Fact (Nat.Prime q)] : Nontrivial (PSL 2 q) := by
  unfold PSL Matrix.ProjectiveSpecialLinearGroup
  refine ⟨QuotientGroup.mk' _ (upper (1 : ZMod q)), 1, ?_⟩
  intro hh
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hh
  exact upper_one_notMem_center (ZMod q) hh

/-! ### The center of `SL(2,F)` — kernel of `SL → PSL` -/

/-- **The center of `SL(2,F)` is `{1, -1}`.** A central element commutes with all
transvections, hence is a scalar matrix `c·I` (`mem_range_scalar_iff_commute_…`);
`det = c² = 1` forces `c = ±1`. This pins the kernel `Z` of `SL(2,q) ↠ PSL(2,q)`,
the groundwork for the Iwasawa `FaithfulSMul` obligation (the `ℙ¹` action of
`SL(2,q)` has kernel exactly `Z`, so `PSL(2,q)` acts faithfully). -/
theorem center_SL2 (F : Type*) [Field F] [DecidableEq F]
    (g : SpecialLinearGroup (Fin 2) F) :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff] at hg
    have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 2) F, Commute t.toMatrix g.val := by
      intro t
      have hSL := hg ⟨t.toMatrix, t.det⟩
      have h2 : t.toMatrix * g.val = g.val * t.toMatrix := by
        have := congrArg (fun x : SpecialLinearGroup (Fin 2) F => x.val) hSL
        simpa [SpecialLinearGroup.coe_mul] using this
      exact h2
    rw [← Matrix.mem_range_scalar_iff_commute_transvectionStruct] at hcomm
    obtain ⟨c, hc⟩ := hcomm
    have hval : g.val = !![c, 0; 0, c] := by
      rw [← hc]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    have hdet : c * c = 1 := by
      have h := g.2; rw [hval] at h; simpa [Matrix.det_fin_two_of] using h
    rcases mul_self_eq_one_iff.mp hdet with h1 | h1
    · left; apply Subtype.ext
      rw [hval, h1]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.coe_one, Matrix.one_apply]
    · right; apply Subtype.ext
      rw [hval, h1]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one, Matrix.one_apply]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Subgroup.mem_center_iff]; intro h; rw [mul_neg_one, neg_one_mul]

end SL2
end FiniteSimpleGroups

import FiniteSimpleGroups.SLnAction
import FiniteSimpleGroups.SLnPerfect
import FiniteSimpleGroups.SLnSimple

/-!
# The Iwasawa structure for `PSL(n,F)` — direction-`v` transvection subgroups

The last Iwasawa obligation for `PSL_isSimpleGroup_rank_ge_three` is an
`IwasawaStructure (PSL n q) ℙ^{n-1}`: a conjugation-equivariant family
`T : ℙ^{n-1} → Subgroup (PSL n q)` of abelian subgroups that generate the group.

For `PSL(n,q)` the natural choice is, for a projective point `[v]`, the **unipotent
radical** of the stabilizer of `[v]`: the abelian group of *transvections with center
direction `v`*,
`{ 1 + v ⊗ φ : φ ∈ (Fⁿ)*, φ(v) = 0 }`.
Here `v ⊗ φ` is the rank-one matrix `vecMulVec v φ` (entries `vᵢ φⱼ`). The constraint
`φ(v) = φ ⬝ᵥ v = 0` makes `v ⊗ φ` nilpotent (`(v⊗φ)(v⊗ψ) = (φ⬝ᵥv)·(v⊗ψ) = 0`), so:

* each `1 + v⊗φ` has `det = 1 + φ(v) = 1` (`dirTransMat_det`), an element of `SL(n,F)`;
* the family is an **abelian** group under multiplication, `(1+v⊗φ)(1+v⊗ψ) = 1+v⊗(φ+ψ)`
  (`dirTransMat_mul`/`dirTransSL_mul`, `dirTransSL_zero`);
* conjugation is **equivariant**: `g(1+v⊗φ)g⁻¹ = 1 + (gv)⊗(φg⁻¹)`, carrying the
  direction-`v` group to the direction-`gv` group (`dirTransMat_conj`/`dirTransSL_conj`,
  with `dotProduct_constraint_conj` checking `(φg⁻¹)(gv) = φ(v) = 0`).

This file builds that **SL-level** machinery (the genuine new content). The descent to
the PSL-level abelian family `Tline`, conjugation-equivariance, generation (which reduces
to the already-disclosed `transvecSL_closure_eq_top`, since every elementary transvection
is such a `1 + eᵢ⊗(c eⱼ)`), and the final `IwasawaStructure` record assembling them is the
remaining step (mirrors `SL2.transvecGroup`/`Tline`).
-/

open Matrix

namespace FiniteSimpleGroups.SLn

variable {n : Type*} [DecidableEq n] [Fintype n] {F : Type*} [Field F]

private theorem sl_mul_inv (g : SpecialLinearGroup n F) : g.val * g⁻¹.val = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

private theorem sl_inv_mul (g : SpecialLinearGroup n F) : g⁻¹.val * g.val = 1 :=
  mul_eq_one_comm.mp (sl_mul_inv g)

/-- The **direction-`v` transvection matrix** `1 + v⊗φ` (`v⊗φ = vecMulVec v φ`). -/
def dirTransMat (v φ : n → F) : Matrix n n F := 1 + vecMulVec v φ

/-- `det (1 + v⊗φ) = 1 + φ(v) = 1` when `φ(v) = φ ⬝ᵥ v = 0` (matrix determinant lemma). -/
theorem dirTransMat_det {v φ : n → F} (h : φ ⬝ᵥ v = 0) : (dirTransMat v φ).det = 1 := by
  rw [dirTransMat, vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow, h,
    add_zero]

/-- The direction-`v` transvection as an element of `SL(n,F)` (for `φ(v) = 0`). -/
def dirTransSL (v φ : n → F) (h : φ ⬝ᵥ v = 0) : SpecialLinearGroup n F :=
  ⟨dirTransMat v φ, dirTransMat_det h⟩

@[simp] theorem dirTransSL_val (v φ : n → F) (h : φ ⬝ᵥ v = 0) :
    (dirTransSL v φ h).val = dirTransMat v φ := rfl

/-- **The transvection group law**: `(1+v⊗φ)(1+v⊗ψ) = 1 + v⊗(φ+ψ)` when `φ(v) = 0` (the
cross term `(v⊗φ)(v⊗ψ) = (φ⬝ᵥv)·(v⊗ψ)` vanishes). -/
theorem dirTransMat_mul {v φ ψ : n → F} (h : φ ⬝ᵥ v = 0) :
    dirTransMat v φ * dirTransMat v ψ = dirTransMat v (φ + ψ) := by
  have hcross : vecMulVec v φ * vecMulVec v ψ = 0 := by
    rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]
  rw [dirTransMat, dirTransMat, dirTransMat, vecMulVec_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add]
  simp only [Matrix.one_mul, Matrix.mul_one, hcross, add_zero]
  abel

/-- The `SL`-level transvection group law: abelian, parametrized by `φ` with `φ(v) = 0`. -/
theorem dirTransSL_mul (v φ ψ : n → F) (hφ : φ ⬝ᵥ v = 0) (hψ : ψ ⬝ᵥ v = 0) :
    dirTransSL v φ hφ * dirTransSL v ψ hψ
      = dirTransSL v (φ + ψ) (by rw [add_dotProduct, hφ, hψ, add_zero]) := by
  apply Subtype.ext
  show dirTransMat v φ * dirTransMat v ψ = dirTransMat v (φ + ψ)
  exact dirTransMat_mul hφ

theorem dirTransSL_zero (v : n → F) : dirTransSL v 0 (zero_dotProduct v) = 1 := by
  apply Subtype.ext
  show dirTransMat v 0 = 1
  rw [dirTransMat, vecMulVec_zero, add_zero]

/-- Conjugation at the matrix level: `g(1+v⊗φ)g⁻¹ = 1 + (gv)⊗(φg⁻¹)`. -/
theorem dirTransMat_conj (g : SpecialLinearGroup n F) (v φ : n → F) :
    g.val * dirTransMat v φ * g⁻¹.val = dirTransMat (g.val *ᵥ v) (φ ᵥ* g⁻¹.val) := by
  rw [dirTransMat, dirTransMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, sl_mul_inv,
    mul_vecMulVec, vecMulVec_mul]

/-- Conjugation preserves the constraint: `(φg⁻¹)(gv) = φ(v) = 0`. -/
theorem dotProduct_constraint_conj (g : SpecialLinearGroup n F) {v φ : n → F} (h : φ ⬝ᵥ v = 0) :
    (φ ᵥ* g⁻¹.val) ⬝ᵥ (g.val *ᵥ v) = 0 := by
  rw [← dotProduct_mulVec, Matrix.mulVec_mulVec, sl_inv_mul, Matrix.one_mulVec, h]

/-- **SL-level conjugation equivariance**: `g · dirTransSL v φ · g⁻¹ = dirTransSL (g·v) (φ∘g⁻¹)`.
This is what makes the Iwasawa family `is_conj`. -/
theorem dirTransSL_conj (g : SpecialLinearGroup n F) (v φ : n → F) (h : φ ⬝ᵥ v = 0) :
    g * dirTransSL v φ h * g⁻¹
      = dirTransSL (g.val *ᵥ v) (φ ᵥ* g⁻¹.val) (dotProduct_constraint_conj g h) := by
  apply Subtype.ext
  show g.val * (dirTransSL v φ h).val * g⁻¹.val
      = (dirTransSL (g.val *ᵥ v) (φ ᵥ* g⁻¹.val) _).val
  simp only [dirTransSL_val]
  exact dirTransMat_conj g v φ

end FiniteSimpleGroups.SLn

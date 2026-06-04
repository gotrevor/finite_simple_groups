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

/-! ### The direction-`v` transvection subgroup and its conjugation equivariance -/

/-- The linear functional `φ ↦ φ ⬝ᵥ v` on row vectors (used to cut out the codirection space). -/
def dotRightₗ (v : n → F) : (n → F) →ₗ[F] F where
  toFun φ := φ ⬝ᵥ v
  map_add' a b := add_dotProduct a b v
  map_smul' c a := by simp [smul_dotProduct]

/-- The codirection space `{φ : φ(v)=0}` (the (n-1)-dim space of functionals killing `v`). -/
def dirKer (v : n → F) : Submodule F (n → F) := LinearMap.ker (dotRightₗ v)

theorem mem_dirKer {v φ : n → F} : φ ∈ dirKer v ↔ φ ⬝ᵥ v = 0 := LinearMap.mem_ker

/-- The parametrizing hom `Multiplicative {φ : φ(v)=0} → SL(n,F)`, `φ ↦ 1 + v⊗φ`; an
additive-to-multiplicative embedding of the abelian codirection space. -/
def dirTransHom (v : n → F) : Multiplicative (dirKer v) →* SpecialLinearGroup n F where
  toFun φ := dirTransSL v (Multiplicative.toAdd φ : dirKer v).val
              (mem_dirKer.mp (Multiplicative.toAdd φ).property)
  map_one' := by
    show dirTransSL v (0 : dirKer v).val _ = 1
    exact dirTransSL_zero v
  map_mul' a b := by
    apply Subtype.ext
    show dirTransMat v ((Multiplicative.toAdd a + Multiplicative.toAdd b : dirKer v) : n → F)
        = dirTransMat v (Multiplicative.toAdd a : dirKer v).val
          * dirTransMat v (Multiplicative.toAdd b : dirKer v).val
    rw [Submodule.coe_add, ← dirTransMat_mul (mem_dirKer.mp (Multiplicative.toAdd a).property)]

/-- **The direction-`v` transvection subgroup** of `SL(n,F)** — the unipotent radical of the
stabilizer of the line `[v]`, an abelian subgroup `{1 + v⊗φ : φ(v)=0} ≅ {φ : φ(v)=0}`. -/
def dirTransvecGroup (v : n → F) : Subgroup (SpecialLinearGroup n F) := (dirTransHom v).range

instance (v : n → F) : IsMulCommutative (dirTransvecGroup v) := by
  unfold dirTransvecGroup; infer_instance

theorem mem_dirTransvecGroup {v : n → F} {y : SpecialLinearGroup n F} :
    y ∈ dirTransvecGroup v ↔ ∃ φ : n → F, ∃ h : φ ⬝ᵥ v = 0, dirTransSL v φ h = y := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨(Multiplicative.toAdd φ : dirKer v).val,
      mem_dirKer.mp (Multiplicative.toAdd φ).property, rfl⟩
  · rintro ⟨φ, h, rfl⟩
    have hmem : φ ∈ dirKer v := mem_dirKer.mpr h
    exact ⟨(⟨φ, hmem⟩ : dirKer v), rfl⟩

/-- Scaling the direction `v` by `a` reparametrizes `1 + (a•v)⊗φ = 1 + v⊗(a•φ)`. -/
theorem dirTransMat_smul (a : F) (v φ : n → F) :
    dirTransMat (a • v) φ = dirTransMat v (a • φ) := by
  rw [dirTransMat, dirTransMat, smul_vecMulVec, vecMulVec_smul]

/-- **The transvection subgroup depends only on the line `[v]`**: scaling `v` by a nonzero
`a` leaves `dirTransvecGroup` unchanged (reparametrize `φ ↦ a•φ`). Needed to define the
PSL-level family on projective points and for generation. -/
theorem dirTransvecGroup_smul {a : F} (ha : a ≠ 0) (v : n → F) :
    dirTransvecGroup (a • v) = dirTransvecGroup v := by
  apply le_antisymm <;> rw [SetLike.le_def] <;> intro y hy <;>
    rw [mem_dirTransvecGroup] at hy ⊢ <;> obtain ⟨φ, h, rfl⟩ := hy
  · have hv : φ ⬝ᵥ v = 0 := by
      rw [dotProduct_smul] at h
      exact (smul_eq_zero.mp h).resolve_left ha
    refine ⟨a • φ, by rw [smul_dotProduct, hv, smul_zero], ?_⟩
    apply Subtype.ext
    rw [dirTransSL_val, dirTransSL_val, dirTransMat_smul]
  · refine ⟨a⁻¹ • φ, by rw [smul_dotProduct, dotProduct_smul, h, smul_zero, smul_zero], ?_⟩
    apply Subtype.ext
    rw [dirTransSL_val, dirTransSL_val, dirTransMat_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- `dirTransvecGroup` of a representative of `[v]` equals that of `v` (line-invariance). -/
theorem dirTransvecGroup_rep (v : n → F) (hv : v ≠ 0) :
    dirTransvecGroup ((Projectivization.mk F v hv).rep) = dirTransvecGroup v := by
  have h2 : Projectivization.mk F ((Projectivization.mk F v hv).rep)
        (Projectivization.rep_nonzero _) = Projectivization.mk F v hv := by
    rw [Projectivization.mk_rep]
  rw [Projectivization.mk_eq_mk_iff] at h2
  obtain ⟨a, ha⟩ := h2
  rw [← ha, Units.smul_def]
  exact dirTransvecGroup_smul (Units.ne_zero a) _

theorem dirTransvecGroup_conj (g : SpecialLinearGroup n F) (v : n → F) :
    (dirTransvecGroup v).map (MulAut.conj g) = dirTransvecGroup (g.val *ᵥ v) := by
  ext y
  simp only [Subgroup.mem_map, mem_dirTransvecGroup]
  constructor
  · rintro ⟨x, ⟨φ, h, rfl⟩, rfl⟩
    refine ⟨φ ᵥ* g⁻¹.val, dotProduct_constraint_conj g h, ?_⟩
    exact (dirTransSL_conj g v φ h).symm
  · rintro ⟨φ, h, rfl⟩
    have hc : (φ ᵥ* g.val) ⬝ᵥ v = 0 := (dotProduct_mulVec φ g.val v).symm.trans h
    refine ⟨dirTransSL v (φ ᵥ* g.val) hc, ⟨φ ᵥ* g.val, hc, rfl⟩, ?_⟩
    show g * dirTransSL v (φ ᵥ* g.val) hc * g⁻¹ = dirTransSL (g.val *ᵥ v) φ h
    rw [dirTransSL_conj g v (φ ᵥ* g.val) hc]
    apply Subtype.ext
    show dirTransMat (g.val *ᵥ v) ((φ ᵥ* g.val) ᵥ* g⁻¹.val) = dirTransMat (g.val *ᵥ v) φ
    rw [vecMul_vecMul, sl_mul_inv, vecMul_one]

/-! ### PSL-level transvection family `Tline` (the Iwasawa `T`)

`Tline x` is the image in `PSL(n,F) = SL/Z` of the direction-`x.rep` transvection subgroup;
by `dirTransvecGroup_rep`/`_smul` it depends only on the line `x`. It is abelian (image of
an abelian subgroup). What remains for the full `IwasawaStructure` record is `is_conj`
(`Tline (g•x) = conj g • Tline x`, from `dirTransvecGroup_conj` pushed through the quotient —
template in `SL2.Tline_conj`) and `is_generator` (`iSup Tline = ⊤`, reducing to
`transvecSL_closure_eq_top` since `transvecSL i j c = dirTransSL eᵢ (c·eⱼ) ∈ dirTransvecGroup eᵢ`). -/

/-- **`PSL(n,F)`-level transvection subgroup along the line `x`** — the image in `SL/Z` of
`dirTransvecGroup x.rep`. The Iwasawa family `T`. -/
noncomputable def Tline (x : Projectivization F (n → F)) :
    Subgroup (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F)) :=
  (dirTransvecGroup x.rep).map (QuotientGroup.mk' (Subgroup.center _))

instance (x : Projectivization F (n → F)) : IsMulCommutative (Tline x) := by
  unfold Tline; infer_instance

theorem Tline_mk (v : n → F) (hv : v ≠ 0) :
    Tline (Projectivization.mk F v hv)
      = (dirTransvecGroup v).map (QuotientGroup.mk' (Subgroup.center _)) :=
  congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center _))) (dirTransvecGroup_rep v hv)

end FiniteSimpleGroups.SLn

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
open scoped Pointwise

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

/-! ### Generation: the family `Tline` generates `PSL(n,F)`

Every elementary transvection `transvecSL i j c` is `1 + eᵢ⊗(c·eⱼ)`, a member of
`dirTransvecGroup eᵢ`; since the elementary transvections generate `SL(n,F)`
(`transvecSL_closure_eq_top`), the images `Tline` generate `PSL = SL/Z`. -/

/-- `(c·eⱼ)(eᵢ) = 0` for `i ≠ j` — the constraint making `1 + eᵢ⊗(c·eⱼ)` a transvection. -/
theorem elem_constraint {i j : n} (hij : i ≠ j) (c : F) :
    (c • (Pi.single j 1 : n → F)) ⬝ᵥ (Pi.single i 1 : n → F) = 0 := by
  rw [smul_dotProduct, single_dotProduct, one_mul, Pi.single_eq_of_ne hij.symm, smul_zero]

/-- **The elementary transvection is a direction-`eᵢ` transvection**: `transvection i j c =
1 + eᵢ⊗(c·eⱼ)`. -/
theorem transvection_eq_dirTransMat {i j : n} (c : F) :
    Matrix.transvection i j c
      = dirTransMat (Pi.single i (1 : F)) (c • (Pi.single j 1 : n → F)) := by
  rw [dirTransMat, Matrix.transvection]
  congr 1
  ext k l
  rw [vecMulVec_apply, Pi.single_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk
    by_cases hl : l = j
    · subst hl; rw [single_apply_same]; simp
    · rw [single_apply_of_col_ne k k (Ne.symm hl)]; simp [hl]
  · rw [single_apply_of_row_ne (Ne.symm hk)]; simp [hk]

/-- `transvecSL i j c ∈ dirTransvecGroup eᵢ` (it is `1 + eᵢ⊗(c·eⱼ)`). -/
theorem transvecSL_mem_dirTransvecGroup {i j : n} (hij : i ≠ j) (c : F) :
    transvecSL hij c ∈ dirTransvecGroup (Pi.single i (1 : F)) := by
  rw [mem_dirTransvecGroup]
  refine ⟨c • (Pi.single j 1 : n → F), elem_constraint hij c, ?_⟩
  apply Subtype.ext
  rw [dirTransSL_val, transvecSL_val]
  exact (transvection_eq_dirTransMat c).symm

/-- **The family `Tline` generates `PSL(n,F)`** — the Iwasawa `is_generator` obligation.
Reduces to `transvecSL_closure_eq_top`: each `transvecSL i j c` lies in `Tline [eᵢ]`, so the
closure of the generators (= `⊤` in `SL`) descends to `iSup Tline = ⊤` in `SL/Z`. -/
theorem Tline_iSup : iSup (Tline (n := n) (F := F)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨y_SL, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) y
  have hsub : {g : SpecialLinearGroup n F | ∃ (i j : n) (h : i ≠ j) (c : F), g = transvecSL h c}
      ⊆ ((iSup Tline).comap (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup n F)))
          : Subgroup (SpecialLinearGroup n F)) := by
    rintro w ⟨i, j, hij, c, rfl⟩
    have hei : (Pi.single i 1 : n → F) ≠ 0 := fun hz => by simpa using congrFun hz i
    refine Subgroup.mem_comap.mpr ?_
    have hmem : QuotientGroup.mk' (Subgroup.center _) (transvecSL hij c)
        ∈ Tline (Projectivization.mk F (Pi.single i 1) hei) := by
      rw [Tline_mk]
      exact Subgroup.mem_map_of_mem _ (transvecSL_mem_dirTransvecGroup hij c)
    exact le_iSup Tline _ hmem
  have hmem : y_SL ∈ (iSup Tline).comap
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup n F))) := by
    have h := (Subgroup.closure_le _).mpr hsub
    rw [transvecSL_closure_eq_top] at h
    exact h (Subgroup.mem_top y_SL)
  exact Subgroup.mem_comap.mp hmem

/-! ### Assembling the Iwasawa criterion: `PSL(n,F)` simple for rank ≥ 3 -/

/-- **The Iwasawa structure on `PSL(n,F) ↷ ℙ^{n-1}`** — the final Iwasawa obligation: the
family `Tline` of abelian transvection subgroups (`is_comm`), conjugation-equivariant
(`is_conj`, via `dirTransvecGroup_conj` through the quotient) and generating (`is_generator`,
`Tline_iSup`). Generalizes `SL2.pslIwasawa` to all ranks. -/
noncomputable def pslnIwasawaStructure :
    letI := pslnAction (n := n) (F := F)
    MulAction.IwasawaStructure
      (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) :=
  letI := pslnAction (n := n) (F := F)
  { T := Tline
    is_comm := fun x => inferInstance
    is_conj := fun g x => by
      obtain ⟨g_SL, hg⟩ := QuotientGroup.mk_surjective g
      have hne : g_SL.val *ᵥ x.rep ≠ 0 := by
        rw [← smul_vec_def]
        exact (smul_ne_zero_iff_ne g_SL).mpr (Projectivization.rep_nonzero x)
      have hgx : g • x = Projectivization.mk F (g_SL.val *ᵥ x.rep) hne := by
        rw [← hg]
        show g_SL • x = Projectivization.mk F (g_SL.val *ᵥ x.rep) hne
        conv_lhs => rw [← Projectivization.mk_rep x]
        rw [Projectivization.smul_mk]; rfl
      have hpar : dirTransvecGroup ((g • x).rep) = dirTransvecGroup (g_SL.val *ᵥ x.rep) := by
        have h2 : Projectivization.mk F ((g • x).rep) (Projectivization.rep_nonzero _)
            = Projectivization.mk F (g_SL.val *ᵥ x.rep) hne := by
          rw [Projectivization.mk_rep]; exact hgx
        rw [Projectivization.mk_eq_mk_iff] at h2
        obtain ⟨a, ha⟩ := h2
        rw [← ha, Units.smul_def]
        exact dirTransvecGroup_smul (Units.ne_zero a) _
      rw [show (MulAut.conj g) • Tline x = (Tline x).map (MulAut.conj g) from
            Subgroup.toSubmonoid_inj.mp rfl]
      rw [Tline, Tline, hpar, ← dirTransvecGroup_conj g_SL]
      simp only [Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun z => ?_
      change (QuotientGroup.mk' (Subgroup.center _)) (g_SL * z * g_SL⁻¹)
          = MulAut.conj g ((QuotientGroup.mk' (Subgroup.center _)) z)
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ← hg]; rfl
    is_generator := Tline_iSup }

/-- **`PSL(n,F)` acts faithfully on `ℙ^{n-1}`** as a `FaithfulSMul` instance (from
`pslnPermHom_injective`) — packaging the Iwasawa `FaithfulSMul` obligation. -/
@[reducible]
noncomputable def pslnFaithful [Nonempty n] :
    letI := pslnAction (n := n) (F := F)
    FaithfulSMul (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) :=
  letI := pslnAction (n := n) (F := F)
  { eq_of_smul_eq_smul := fun {g₁ g₂} hsmul => by
      apply pslnPermHom_injective
      ext x
      exact hsmul x }

/-- **`PSL(n,F) = SL(n,F)/Z` is simple for `3 ≤ |n|`** — the Iwasawa criterion
(`IwasawaStructure.isSimpleGroup`) applied to the action on `ℙ^{n-1}`, with all six
obligations assembled: perfect (`commutator_PSLn_eq_top`), nontrivial (`PSLn_nontrivial`),
MulAction (`pslnAction`), faithful (`pslnFaithful`), quasi-preprimitive
(`pslnQuasiPreprimitive`), and the `IwasawaStructure` (`pslnIwasawaStructure`). Discharges
`PSL_isSimpleGroup_rank_ge_three` modulo the two disclosed geometric axioms
`transvecSL_closure_eq_top` and `exists_sl_maps_two_points`. -/
theorem PSLn_isSimpleGroup_of_rank [Nonempty n] (h3 : 3 ≤ Fintype.card n) :
    IsSimpleGroup (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F)) := by
  letI := pslnAction (n := n) (F := F)
  haveI : Nontrivial (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F)) :=
    PSLn_nontrivial (by omega)
  haveI : FaithfulSMul (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) := pslnFaithful
  haveI : MulAction.IsQuasiPreprimitive
      (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) := pslnQuasiPreprimitive (by omega)
  exact pslnIwasawaStructure.isSimpleGroup (commutator_PSLn_eq_top h3) pslnFaithful

end FiniteSimpleGroups.SLn

import FiniteSimpleGroups.SpAction
import FiniteSimpleGroups.SpTransvection

/-!
# Faithfulness of the `PSp(2n,q)` action on `ℙ²ⁿ⁻¹` — kernel = center

Toward the symplectic Iwasawa criterion for `PSp_isSimpleGroup`, this file establishes that
the kernel of the `Sp(2n,F)`-action on `ℙ²ⁿ⁻¹` is exactly the center, so the quotient
`PSp = Sp/Z` acts **faithfully**. Two directions:

* **`ker ⊆ center`** (`sp_mem_center_of_smul_eq`): a symplectic matrix fixing *every* line is a
  scalar matrix (the eigenvector/standard-basis argument, identical to `SLn.mem_center_of_smul_eq`
  — purely about the linear `mulVec` action), and a scalar matrix is central because it commutes
  with everything.
* **`center ⊆ ker`** (`sp_center_fixes_line`): a central element commutes with every transvection
  `τ_{v,c}`, and `spTransvecSp_conj` turns that into `τ_{g·v,c} = τ_{v,c}`, forcing `g·v ∈ span{v}`
  (the rank-one term `v ⊗ J·v` determines the line `[v]`). This is the genuinely symplectic half,
  built on the conjugation-equivariance `spTransvection_conj`.
-/

open Matrix

namespace FiniteSimpleGroups.SpN

variable {l : Type*} [DecidableEq l] [Fintype l] {F : Type*} [Field F]

/-- If `g ∈ Sp` fixes the line `[v]` (for `v ≠ 0`), then `g·v` is a scalar multiple of `v`. -/
theorem sp_parallel_of_fixes (g : symplecticGroup l F)
    (h : ∀ x : Projectivization F ((l ⊕ l) → F), g • x = x)
    (v : (l ⊕ l) → F) (hv : v ≠ 0) :
    ∃ a : Fˣ, (a : F) • v = (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v := by
  have hx := h (Projectivization.mk _ v hv)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by
    rw [show (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v = g • v from (smul_vec_def g v).symm,
      ← Units.smul_def]; exact ha⟩

/-- **A symplectic matrix fixing every line of `ℙ²ⁿ⁻¹` is a scalar matrix.** Every nonzero
vector is an eigenvector; testing the standard basis `e_i` (columns are `aᵢ·eᵢ`, so `g` is
diagonal) and the vectors `eᵢ + e_{i₀}` (forcing all `aᵢ` equal) shows `↑g = scalar r`. The
argument is identical to `SLn.mem_center_of_smul_eq` (it only uses the linear `mulVec` action). -/
theorem eq_scalar_of_fixes [Nonempty l] (g : symplecticGroup l F)
    (h : ∀ x : Projectivization F ((l ⊕ l) → F), g • x = x) :
    ∃ r : F, (g : Matrix (l ⊕ l) (l ⊕ l) F) = Matrix.scalar (l ⊕ l) r := by
  have col : ∀ i : l ⊕ l, ∃ a : Fˣ, ∀ j,
      (g : Matrix (l ⊕ l) (l ⊕ l) F) j i = (a : F) * (Pi.single i 1 : (l ⊕ l) → F) j := by
    intro i
    have hsi : (Pi.single i 1 : (l ⊕ l) → F) ≠ 0 := fun hz => by simpa using congrFun hz i
    obtain ⟨a, ha⟩ := sp_parallel_of_fixes g h (Pi.single i 1) hsi
    refine ⟨a, fun j => ?_⟩
    have e := congrFun ha j
    rw [mulVec_single_one] at e
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at e
    exact e.symm
  choose a ha using col
  have hoff : ∀ i j : l ⊕ l, j ≠ i → (g : Matrix (l ⊕ l) (l ⊕ l) F) j i = 0 :=
    fun i j hji => by rw [ha i j, Pi.single_eq_of_ne hji, mul_zero]
  have hdiagval : ∀ i : l ⊕ l, (g : Matrix (l ⊕ l) (l ⊕ l) F) i i = (a i : F) :=
    fun i => by rw [ha i i, Pi.single_eq_same, mul_one]
  obtain ⟨i0⟩ := (inferInstance : Nonempty (l ⊕ l))
  have hAllEq : ∀ i : l ⊕ l, (a i : F) = (a i0 : F) := by
    intro i
    by_cases hi : i = i0
    · rw [hi]
    · have hw : (Pi.single i 1 + Pi.single i0 1 : (l ⊕ l) → F) ≠ 0 := fun hz => by
        have := congrFun hz i
        rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hi, add_zero] at this
        exact one_ne_zero this
      obtain ⟨b, hb⟩ := sp_parallel_of_fixes g h _ hw
      have ei := congrFun hb i
      have ei0 := congrFun hb i0
      rw [Matrix.mulVec_add, mulVec_single_one, mulVec_single_one] at ei ei0
      have lhsi : ((b : F) • (Pi.single i 1 + Pi.single i0 1 : (l ⊕ l) → F)) i = (b : F) := by
        simp [Pi.single_eq_same, Pi.single_eq_of_ne hi]
      have lhsi0 : ((b : F) • (Pi.single i 1 + Pi.single i0 1 : (l ⊕ l) → F)) i0 = (b : F) := by
        simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi)]
      have rhsi : ((g : Matrix (l ⊕ l) (l ⊕ l) F).col i
          + (g : Matrix (l ⊕ l) (l ⊕ l) F).col i0) i = (a i : F) := by
        simp only [Pi.add_apply, Matrix.col_apply]
        rw [hdiagval i, hoff i0 i hi, add_zero]
      have rhsi0 : ((g : Matrix (l ⊕ l) (l ⊕ l) F).col i
          + (g : Matrix (l ⊕ l) (l ⊕ l) F).col i0) i0 = (a i0 : F) := by
        simp only [Pi.add_apply, Matrix.col_apply]
        rw [hdiagval i0, hoff i i0 (Ne.symm hi), zero_add]
      rw [lhsi, rhsi] at ei
      rw [lhsi0, rhsi0] at ei0
      rw [← ei, ← ei0]
  refine ⟨(a i0 : F), ?_⟩
  ext i j
  rw [Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; rw [diagonal_apply_eq, hdiagval i, hAllEq i]
  · rw [diagonal_apply_ne _ hij, hoff j i hij]

/-- **`ker ⊆ center`**: a symplectic element fixing every line is central (it is a scalar
matrix, which commutes with everything). -/
theorem sp_mem_center_of_smul_eq [Nonempty l] (g : symplecticGroup l F)
    (h : ∀ x : Projectivization F ((l ⊕ l) → F), g • x = x) :
    g ∈ Subgroup.center (symplecticGroup l F) := by
  obtain ⟨r, hr⟩ := eq_scalar_of_fixes g h
  rw [Subgroup.mem_center_iff]
  intro hh
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, hr]
  exact (Matrix.scalar_commute r (fun r' => mul_comm r r')
    (hh : Matrix (l ⊕ l) (l ⊕ l) F)).symm

/-- `J·v ≠ 0` for `v ≠ 0` (`J` is invertible: `J·J = -1`). -/
theorem mulVec_J_ne_zero {v : (l ⊕ l) → F} (hv : v ≠ 0) : Matrix.J l F *ᵥ v ≠ 0 := by
  intro h0
  apply hv
  have : Matrix.J l F *ᵥ (Matrix.J l F *ᵥ v) = 0 := by rw [h0, mulVec_zero]
  rw [mulVec_mulVec, J_squared, neg_mulVec, one_mulVec] at this
  exact neg_eq_zero.mp this

/-- **`center ⊆ ker`**: a central element of `Sp` fixes every line of `ℙ²ⁿ⁻¹`. A central `g`
commutes with the transvection `τ_{v,1}`, so by `spTransvecSp_conj`, `τ_{g·v,1} = τ_{v,1}`,
hence `(g·v) ⊗ J(g·v) = v ⊗ J·v`. The rank-one term determines the line `[v]`: evaluating a
column where `J·v` is nonzero forces `g·v ∈ span{v}`. -/
theorem sp_center_fixes_line [Nonempty l] (g : symplecticGroup l F)
    (hg : g ∈ Subgroup.center (symplecticGroup l F))
    (x : Projectivization F ((l ⊕ l) → F)) : g • x = x := by
  set v := x.rep with hv_def
  have hv : v ≠ 0 := Projectivization.rep_nonzero x
  set w := (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ v with hw_def
  -- central ⇒ conjugation by `g` fixes the transvection `τ_{v,1}`
  have hc := Subgroup.mem_center_iff.mp hg (spTransvecSp v 1)
  have hconj : g * spTransvecSp v 1 * g⁻¹ = spTransvecSp v 1 := by
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have heq : spTransvecSp w 1 = spTransvecSp v 1 :=
    (spTransvecSp_conj g v 1).symm.trans hconj
  -- pass to the rank-one matrices: `w ⊗ J·w = v ⊗ J·v`
  have hM : vecMulVec w (Matrix.J l F *ᵥ w) = vecMulVec v (Matrix.J l F *ᵥ v) := by
    have hval : spTransvection w 1 = spTransvection v 1 := by
      have := congrArg (fun y : symplecticGroup l F => (y : Matrix (l ⊕ l) (l ⊕ l) F)) heq
      simpa only [spTransvecSp_coe] using this
    rw [spTransvection, spTransvection, one_smul, one_smul] at hval
    exact add_left_cancel hval
  -- choose a column where `J·v` is nonzero
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp (mulVec_J_ne_zero hv)
  rw [Pi.zero_apply] at hj0
  -- that column gives `(J·w) j0 • w = (J·v) j0 • v`
  have hcol : (Matrix.J l F *ᵥ w) j0 • w = (Matrix.J l F *ᵥ v) j0 • v := by
    funext i
    have hij := congrFun (congrFun hM i) j0
    rw [vecMulVec_apply, vecMulVec_apply] at hij
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_comm ((Matrix.J l F *ᵥ w) j0), mul_comm ((Matrix.J l F *ᵥ v) j0)]
    exact hij
  have hdv : (Matrix.J l F *ᵥ v) j0 • v ≠ 0 := smul_ne_zero hj0 hv
  have hcw : (Matrix.J l F *ᵥ w) j0 ≠ 0 := fun h0 => hdv (by rw [← hcol, h0, zero_smul])
  -- hence `w = a • v` with `a ≠ 0`
  set a : F := ((Matrix.J l F *ᵥ w) j0)⁻¹ * (Matrix.J l F *ᵥ v) j0 with ha_def
  have hwv : a • v = w := by
    rw [ha_def, ← smul_smul, ← hcol, smul_smul, inv_mul_cancel₀ hcw, one_smul]
  -- conclude `g • x = x`
  have hgvw : g • v = w := (smul_vec_def g v).trans hw_def.symm
  have hx : Projectivization.mk F v hv = x := Projectivization.mk_rep x
  rw [← hx, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨a, hwv.trans hgvw.symm⟩

end FiniteSimpleGroups.SpN

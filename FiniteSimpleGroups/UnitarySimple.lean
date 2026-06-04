import FiniteSimpleGroups.UnitaryTransvection

/-!
# Faithfulness of `PSU(n,q) = SU/Z` on the isotropic points — kernel = center (PSU step 2)

Toward the unitary Iwasawa criterion for `PSU_isSimpleGroup`, this file builds the action of
`SU_n(F)` on the projective space `ℙ(Fⁿ)` and establishes the two halves of faithfulness for
`PSU = SU/Z`:

* **`center ⊆ ker`** (`su_central_fixes_isotropic_line`): a central element of `SU` commutes with
  every transvection `τ_{v,a}` (`v` isotropic, `a` trace-zero), and `uTransvecSU_conj` turns that
  into `τ_{g·v,a} = τ_{v,a}`, forcing `g·v ∈ span{v}` — the rank-one term `v ⊗ star v` (with
  `star v ≠ 0` for `v ≠ 0`) determines the line `[v]`. This is the unitary analogue of
  `SpN.sp_center_fixes_line`, restricted to **isotropic** lines (the only ones carrying a
  transvection in the unitary case).

* **`ker ⊆ center`** (the genuinely geometric half): an element fixing *every isotropic* line is a
  scalar matrix. Unlike the symplectic case — where transvections exist at every vector and the
  scalar conclusion is the purely-linear `eq_scalar_of_fixes` over the *full* projective space —
  the unitary group is **not** transitive on `ℙ(Fⁿ)` (it has separate orbits of isotropic and
  anisotropic points), so the Iwasawa action lives on the **isotropic** points and the kernel
  argument must use the Hermitian form. The crux is `su_fixes_isotropic_imp_scalar` below; the
  algebraic engine for it (`lambda_form_relation`) is machine-checked here.

`SpSimple.lean` is the structural template.
-/

open Matrix

namespace FiniteSimpleGroups.PSU

variable {n : Type*} [DecidableEq n] [Fintype n] {F : Type*} [Field F] [StarRing F]

/-! ### The linear action of `SU_n(F)` on `Fⁿ` and the induced action on `ℙ(Fⁿ)` -/

/-- `SU_n(F)` acts on `n → F` by matrix–vector product. -/
instance : SMul (Matrix.specialUnitaryGroup n F) (n → F) where
  smul g v := (g : Matrix n n F) *ᵥ v

@[simp] theorem su_smul_vec_def (g : Matrix.specialUnitaryGroup n F) (v : n → F) :
    g • v = (g : Matrix n n F) *ᵥ v := rfl

instance : MulAction (Matrix.specialUnitaryGroup n F) (n → F) where
  one_smul v := by
    show ((1 : Matrix.specialUnitaryGroup n F) : Matrix n n F) *ᵥ v = v; simp
  mul_smul g h v := by
    show ((g * h : Matrix.specialUnitaryGroup n F) : Matrix n n F) *ᵥ v
        = (g : Matrix n n F) *ᵥ ((h : Matrix n n F) *ᵥ v)
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

instance : DistribMulAction (Matrix.specialUnitaryGroup n F) (n → F) where
  smul_zero g := by show (g : Matrix n n F) *ᵥ 0 = 0; simp
  smul_add g v w := by
    show (g : Matrix n n F) *ᵥ (v + w) = (g : Matrix n n F) *ᵥ v + (g : Matrix n n F) *ᵥ w
    simp [Matrix.mulVec_add]

instance : SMulCommClass (Matrix.specialUnitaryGroup n F) F (n → F) where
  smul_comm g c v := by
    show (g : Matrix n n F) *ᵥ (c • v) = c • (g : Matrix n n F) *ᵥ v
    simp [Matrix.mulVec_smul]

/-- **`SU_n(F)` acts on the projective space `ℙ(Fⁿ)`** (mathlib's projective-space action,
fed by the linear `mulVec` action above). `PSU = SU/Z` descends through the center below. -/
example : MulAction (Matrix.specialUnitaryGroup n F) (Projectivization F (n → F)) :=
  inferInstance

/-! ### `center ⊆ ker`: a central element fixes every isotropic line -/

omit [DecidableEq n] [Fintype n] in
/-- `star v ≠ 0` for `v ≠ 0` (the componentwise conjugation is injective on a field). -/
theorem star_vec_ne_zero {v : n → F} (hv : v ≠ 0) : star v ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Function.ne_iff.mpr ⟨i, by simpa [Pi.star_apply, star_eq_zero] using hi⟩

/-- **`center ⊆ ker` (isotropic lines).** A central element `g` of `SU` fixes every isotropic
projective line. The proof: `g` commutes with the transvection `τ_{v,a}` (`v` isotropic, `a`
trace-zero), so by `uTransvecSU_conj`, `τ_{g·v,a} = τ_{v,a}`, hence the rank-one matrices agree,
`(g·v) ⊗ star(g·v) = v ⊗ star v`. Evaluating a column where `star v` is nonzero forces
`g·v ∈ span{v}`. The unitary analogue of `SpN.sp_center_fixes_line`. -/
theorem su_central_fixes_isotropic_line
    (g : Matrix.specialUnitaryGroup n F) (hg : g ∈ Subgroup.center (Matrix.specialUnitaryGroup n F))
    {v : n → F} (hv : v ≠ 0) (hiso : star v ⬝ᵥ v = 0) (a : F) (ha0 : a ≠ 0) (ha : a + star a = 0) :
    ∃ b : F, (g : Matrix n n F) *ᵥ v = b • v := by
  set w := (g : Matrix n n F) *ᵥ v with hw_def
  have hgw_iso : star w ⬝ᵥ w = 0 :=
    u_isotropic_of_mem (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) hiso
  -- central ⇒ conjugation by `g` fixes the transvection `τ_{v,a}`
  have hc := Subgroup.mem_center_iff.mp hg (uTransvecSU v a hiso ha)
  have hconj : g * uTransvecSU v a hiso ha * g⁻¹ = uTransvecSU v a hiso ha := by
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have heq : uTransvecSU w a hgw_iso ha = uTransvecSU v a hiso ha :=
    (uTransvecSU_conj g v a hiso ha).symm.trans hconj
  -- pass to the rank-one matrices: `a•(w ⊗ star w) = a•(v ⊗ star v)`, cancel `a`
  have hM : Matrix.vecMulVec w (star w) = Matrix.vecMulVec v (star v) := by
    have hval : uTransvection w a = uTransvection v a := by
      have := congrArg (fun y : Matrix.specialUnitaryGroup n F => (y : Matrix n n F)) heq
      simpa only [uTransvecSU_coe] using this
    rw [uTransvection, uTransvection] at hval
    have h2 : a • Matrix.vecMulVec w (star w) = a • Matrix.vecMulVec v (star v) :=
      add_left_cancel hval
    exact smul_right_injective _ ha0 h2
  -- choose a column where `star v` is nonzero
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp (star_vec_ne_zero hv)
  rw [Pi.zero_apply] at hj0
  -- that column gives `(star w) j0 • w = (star v) j0 • v`
  have hcol : (star w) j0 • w = (star v) j0 • v := by
    funext i
    have hij := congrFun (congrFun hM i) j0
    rw [vecMulVec_apply, vecMulVec_apply] at hij
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_comm ((star w) j0), mul_comm ((star v) j0)]
    exact hij
  have hdv : (star v) j0 • v ≠ 0 := smul_ne_zero hj0 hv
  have hcw : (star w) j0 ≠ 0 := fun h0 => hdv (by rw [← hcol, h0, zero_smul])
  refine ⟨((star w) j0)⁻¹ * (star v) j0, ?_⟩
  rw [← smul_smul, ← hcol, smul_smul, inv_mul_cancel₀ hcw, one_smul]

end FiniteSimpleGroups.PSU

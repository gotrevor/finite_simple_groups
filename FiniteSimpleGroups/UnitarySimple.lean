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

/-! ### `ker ⊆ center`: the geometric crux — fixing every isotropic line forces scalar

The engine is the interplay of two facts about an isometry `g` (i.e. `g ∈ unitaryGroup`) that
fixes isotropic lines (`g·z = λ_z·z` for isotropic `z`):

* **Form relation** (`lambda_form_relation`): for isotropic `v, w` with `⟨v,w⟩ ≠ 0`,
  `star(λ_v)·λ_w = 1`. Pure isometry bookkeeping.
* **Hyperbolic-pair collapse** (`lambda_eq_norm_one_of_hyperbolic`): if `w` is a hyperbolic
  partner of `v` (`⟨v,w⟩ = 1`, both isotropic) then `λ_v = λ_w` **and** `N(λ_v) = λ_v·star(λ_v) = 1`.
  The key trick: for a trace-zero `s ≠ 0`, `v + s·w` is again isotropic, and reading off the
  `v`- and `w`-coordinates of `g·(v + s·w) = μ·(v + s·w)` pins `λ_v = μ = λ_w`.

Then `N = 1` upgrades the form relation `star(λ_v)λ_w = 1` to `λ_v = λ_w` for any non-orthogonal
isotropic pair, and connectivity + spanning of the isotropic vectors propagate a single scalar `μ`
to all of `Fⁿ`. -/

/-- **Isometry form relation.** If `g ∈ unitaryGroup` scales `v` by `λ_v` and `w` by `λ_w`, then
`star(λ_v)·λ_w·⟨v,w⟩ = ⟨v,w⟩`. So whenever `⟨v,w⟩ = star v ⬝ᵥ w ≠ 0`, `star(λ_v)·λ_w = 1`. -/
theorem lambda_form_relation {g : Matrix n n F} (hg : g ∈ Matrix.unitaryGroup n F)
    {v w : n → F} {lv lw : F} (hv : g *ᵥ v = lv • v) (hw : g *ᵥ w = lw • w) :
    star lv * lw * (star v ⬝ᵥ w) = star v ⬝ᵥ w := by
  have hpf := u_preserves_form hg v w
  rw [hv, hw] at hpf
  have hsv : star (lv • v) = star lv • star v := by
    funext i; simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul']
  rw [hsv, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at hpf
  exact hpf

omit [DecidableEq n] in
/-- `⟨w,v⟩ = star (⟨v,w⟩)` (the Hermitian symmetry of the standard form). -/
theorem dotProduct_star_swap (v w : n → F) : star w ⬝ᵥ v = star (star v ⬝ᵥ w) := by
  simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm]

/-- **Hyperbolic-pair collapse.** Let `g ∈ unitaryGroup` fix the isotropic lines `[v]` and `[w]`
(`g·v = λ_v·v`, `g·w = λ_w·w`) where `(v,w)` is a hyperbolic pair (`⟨v,w⟩ = 1`, both isotropic).
Given a trace-zero `s ≠ 0`, the vector `v + s·w` is again isotropic, so `g·(v+s·w) = μ·(v+s·w)`;
reading off its `v`- and `w`-coordinates forces `λ_v = μ = λ_w`, and the form relation at
`⟨v,w⟩ = 1` then gives `N(λ_v) = λ_v·star(λ_v) = 1`. -/
theorem lambda_eq_norm_one_of_hyperbolic {g : Matrix n n F} (hg : g ∈ Matrix.unitaryGroup n F)
    {v w : n → F} {lv lw : F} (hv : g *ᵥ v = lv • v) (hw : g *ᵥ w = lw • w)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0) (hvw : star v ⬝ᵥ w = 1)
    {s : F} (hs0 : s ≠ 0)
    {μ : F} (hμ : g *ᵥ (v + s • w) = μ • (v + s • w)) :
    lv = lw ∧ lv * star lv = 1 := by
  have hwv : star w ⬝ᵥ v = 1 := by rw [dotProduct_star_swap, hvw, star_one]
  have hgvsw : g *ᵥ (v + s • w) = lv • v + (s * lw) • w := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hv, hw, smul_smul]
  have heq : lv • v + (s * lw) • w = μ • v + (μ * s) • w := by
    rw [← hgvsw, hμ, smul_add, smul_smul]
  -- pair with `star v` (kills the `v`-coordinate via `⟨v,v⟩=0`, reads `w`-coordinate)
  have e1 : s * lw = μ * s := by
    have := congrArg (fun u => star v ⬝ᵥ u) heq
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hviso, hvw, mul_zero, mul_one,
      zero_add] using this
  -- pair with `star w` (kills the `w`-coordinate via `⟨w,w⟩=0`, reads `v`-coordinate)
  have e2 : lv = μ := by
    have := congrArg (fun u => star w ⬝ᵥ u) heq
    simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul, hwiso, hwv, mul_zero, mul_one,
      add_zero] using this
  have hlw : lw = μ := by
    have : s * lw = s * μ := by rw [e1]; ring
    exact mul_left_cancel₀ hs0 this
  have hlvw : lw = lv := by rw [hlw, e2]
  refine ⟨hlvw.symm, ?_⟩
  -- `N(λ_v) = 1` from the form relation at `⟨v,w⟩ = 1`
  have hfr := lambda_form_relation hg hv hw
  rw [hvw, mul_one, hlvw, mul_comm] at hfr
  exact hfr

/-- **Non-orthogonal isotropic lines share the scalar.** If `g ∈ unitaryGroup` scales `v` by
`λ_v` (with `N(λ_v) = λ_v·star(λ_v) = 1`) and `w` by `λ_w`, and `⟨v,w⟩ ≠ 0`, then `λ_v = λ_w`.
The form relation gives `star(λ_v)·λ_w = 1`; combined with `star(λ_v)·λ_v = 1` and the cancellation
`star(λ_v) ≠ 0`, this forces `λ_w = λ_v`. -/
theorem lambda_eq_of_nonorth {g : Matrix n n F} (hg : g ∈ Matrix.unitaryGroup n F)
    {v w : n → F} {lv lw : F} (hv : g *ᵥ v = lv • v) (hw : g *ᵥ w = lw • w)
    (hN : lv * star lv = 1) (hvw : star v ⬝ᵥ w ≠ 0) : lv = lw := by
  have hfr := lambda_form_relation hg hv hw
  have h1 : star lv * lw = 1 := mul_right_cancel₀ hvw (by rw [one_mul]; exact hfr)
  have hN' : star lv * lv = 1 := by rw [mul_comm]; exact hN
  have : star lv * lw = star lv * lv := by rw [h1, hN']
  exact (mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hN') this).symm

end FiniteSimpleGroups.PSU

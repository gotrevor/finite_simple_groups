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

/-- **The geometric crux — fixing every isotropic line forces a scalar.** Let `g ∈ unitaryGroup`
fix every isotropic projective line (`hfix`). From three standard facts about the Hermitian
geometry — every nonzero isotropic vector has a **hyperbolic partner** (`hHyp`), any two isotropic
points have a **common non-orthogonal** isotropic point (`hConn`, diameter-2 connectivity), and the
isotropic vectors **span** `Fⁿ` (`hSpan`) — plus the existence of a trace-zero scalar (`htz`) and
of some isotropic vector (`hex`), `g` is a scalar matrix `μ • 1`.

The geometry hypotheses are exactly the finite-Hermitian-geometry facts that hold for the standard
form on `(F_{q²})ⁿ`, `n ≥ 3` (to be supplied/discharged separately); everything else — the
propagation of a single scalar `μ` through the connectivity graph and across the spanning set — is
machine-checked here. -/
theorem su_fixes_isotropic_imp_scalar {g : Matrix n n F} (hg : g ∈ Matrix.unitaryGroup n F)
    (hfix : ∀ z : n → F, star z ⬝ᵥ z = 0 → ∃ l : F, g *ᵥ z = l • z)
    (hHyp : ∀ z : n → F, z ≠ 0 → star z ⬝ᵥ z = 0 → ∃ w : n → F, star w ⬝ᵥ w = 0 ∧ star z ⬝ᵥ w = 1)
    (hConn : ∀ z₁ z₂ : n → F, z₁ ≠ 0 → z₂ ≠ 0 → star z₁ ⬝ᵥ z₁ = 0 → star z₂ ⬝ᵥ z₂ = 0 →
      ∃ u : n → F, u ≠ 0 ∧ star u ⬝ᵥ u = 0 ∧ star z₁ ⬝ᵥ u ≠ 0 ∧ star z₂ ⬝ᵥ u ≠ 0)
    (hSpan : Submodule.span F {z : n → F | star z ⬝ᵥ z = 0} = ⊤)
    (htz : ∃ s : F, s ≠ 0 ∧ s + star s = 0)
    (hex : ∃ v₀ : n → F, v₀ ≠ 0 ∧ star v₀ ⬝ᵥ v₀ = 0) :
    ∃ μ : F, (g : Matrix n n F) = μ • 1 := by
  obtain ⟨s, hs0, hstr⟩ := htz
  -- For each nonzero isotropic `z`: a scaling factor of norm one.
  have key : ∀ z : n → F, z ≠ 0 → star z ⬝ᵥ z = 0 → ∃ l : F, g *ᵥ z = l • z ∧ l * star l = 1 := by
    intro z hz hziso
    obtain ⟨w, hwiso, hzw⟩ := hHyp z hz hziso
    obtain ⟨lz, hlz⟩ := hfix z hziso
    obtain ⟨lw, hlw⟩ := hfix w hwiso
    have hwz : star w ⬝ᵥ z = 1 := by rw [dotProduct_star_swap, hzw, star_one]
    have hsw_iso : star (z + s • w) ⬝ᵥ (z + s • w) = 0 := by
      have hss : star (z + s • w) = star z + star s • star w := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_add, star_mul']
      rw [hss]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        hziso, hzw, hwz, hwiso, mul_zero, mul_one, add_zero, zero_add]
      linear_combination hstr
    obtain ⟨μ, hμ⟩ := hfix (z + s • w) hsw_iso
    obtain ⟨-, hN⟩ := lambda_eq_norm_one_of_hyperbolic hg hlz hlw hziso hwiso hzw hs0 hμ
    exact ⟨lz, hlz, hN⟩
  -- Reference isotropic vector and its (norm-one) scalar `μ`.
  obtain ⟨v₀, hv₀, hv₀iso⟩ := hex
  obtain ⟨μ, hμ, hμN⟩ := key v₀ hv₀ hv₀iso
  -- Every nonzero isotropic `z` is scaled by the *same* `μ`.
  have hconst : ∀ z : n → F, z ≠ 0 → star z ⬝ᵥ z = 0 → g *ᵥ z = μ • z := by
    intro z hz hziso
    obtain ⟨lz, hlz, hlzN⟩ := key z hz hziso
    obtain ⟨u, hu0, huiso, h0u, hzu⟩ := hConn v₀ z hv₀ hz hv₀iso hziso
    obtain ⟨lu, hlu, -⟩ := key u hu0 huiso
    have e1 : μ = lu := lambda_eq_of_nonorth hg hμ hlu hμN h0u
    have e2 : lz = lu := lambda_eq_of_nonorth hg hlz hlu hlzN hzu
    rw [hlz, e2, ← e1]
  -- Extend `g·z = μ•z` from isotropic `z` to all of `Fⁿ` via spanning.
  set M : Matrix n n F := (g : Matrix n n F) - μ • 1 with hM_def
  have hMiso : ∀ z : n → F, star z ⬝ᵥ z = 0 → M *ᵥ z = 0 := by
    intro z hziso
    rcases eq_or_ne z 0 with h0 | h0
    · subst h0; simp [hM_def]
    · rw [hM_def, Matrix.sub_mulVec, hconst z h0 hziso, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_self]
  have hMall : ∀ x : n → F, M *ᵥ x = 0 := by
    have hsub : Submodule.span F {z : n → F | star z ⬝ᵥ z = 0} ≤
        LinearMap.ker (Matrix.mulVecLin M) := by
      rw [Submodule.span_le]
      intro z hz
      exact LinearMap.mem_ker.mpr (by simpa [Matrix.mulVecLin_apply] using hMiso z hz)
    rw [hSpan, top_le_iff] at hsub
    intro x
    have : x ∈ LinearMap.ker (Matrix.mulVecLin M) := by rw [hsub]; exact Submodule.mem_top
    simpa [Matrix.mulVecLin_apply] using LinearMap.mem_ker.mp this
  have hM0 : M = 0 := by
    ext i j
    have hcol := congrFun (hMall (Pi.single j 1)) i
    rw [mulVec_single_one, Matrix.col_apply] at hcol
    simpa using hcol
  exact ⟨μ, by rw [← sub_eq_zero, ← hM_def, hM0]⟩

/-- **Scalar matrices are central** (the easy converse). If `g ∈ SU` is `μ • 1` then it commutes
with every element of `SU`. -/
theorem su_scalar_mem_center {g : Matrix.specialUnitaryGroup n F} {μ : F}
    (hg : (g : Matrix n n F) = μ • 1) :
    g ∈ Subgroup.center (Matrix.specialUnitaryGroup n F) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, hg, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- The vector `eᵢ + c·eⱼ` (`i ≠ j`, `N(c) = c·star c = -1`) is isotropic:
`⟨eᵢ + c eⱼ, eᵢ + c eⱼ⟩ = 1 + star c·c = 1 + N(c) = 0`. -/
theorem isotropic_single_pair {i j : n} (hij : i ≠ j) {c : F} (hc : c * star c = -1) :
    star ((Pi.single i 1 : n → F) + Pi.single j c) ⬝ᵥ
      ((Pi.single i 1 : n → F) + Pi.single j c) = 0 := by
  rw [star_add, ← Pi.single_star, ← Pi.single_star, star_one]
  simp only [add_dotProduct, dotProduct_add, single_dotProduct, Pi.single_eq_same,
    Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, mul_one, mul_zero, add_zero, zero_add]
  rw [mul_comm (star c) c, hc]; ring

/-! ### The center of `SU_n(F_{p²})` is the scalar matrices (`n ≥ 3`)

Instantiating the geometric crux over the concrete Hermitian field `F_{p²} = UnitaryField p`.
Three finite-Hermitian-geometry existence facts remain as **disclosed axioms** — each is standard
and true for the standard form on `(F_{p²})ⁿ`, `n ≥ 3` — feeding the fully machine-checked
`su_fixes_isotropic_imp_scalar`. The trace-zero scalar and an isotropic vector are already
discharged (`UnitaryField.exists_traceZero_ne_zero`, `UnitaryField.exists_isotropic`). -/

section Concrete

variable (p : ℕ) [Fact p.Prime] {n : ℕ}

open UnitaryField

/-- **Hyperbolic partner exists** (machine-checked). Every nonzero isotropic `z` in `(F_{p²})ⁿ`
has an isotropic `w` with `⟨z,w⟩ = 1`. Construction: pick a coordinate `k` with `z k ≠ 0`, so
`⟨z, e_k⟩ = star(z k) =: d ≠ 0`; the rescaled `w₁ = d⁻¹·e_k` has `⟨z,w₁⟩ = 1`, and
`⟨w₁,w₁⟩ = d⁻¹·star(d⁻¹)` is a **norm** hence a trace value, so `exists_add_star_eq_neg_norm`
gives `t` with `t + star t = -⟨w₁,w₁⟩`; then `w = w₁ + t·z` is isotropic (the trace correction)
and still has `⟨z,w⟩ = 1` (since `z` is isotropic). The `hn` hypothesis is unused (holds for
`n ≥ 1`) but kept for a uniform geometry interface. -/
theorem exists_hyperbolic_partner (_hn : 3 ≤ n) :
    ∀ z : Fin n → UnitaryField p, z ≠ 0 → star z ⬝ᵥ z = 0 →
      ∃ w : Fin n → UnitaryField p, star w ⬝ᵥ w = 0 ∧ star z ⬝ᵥ w = 1 := by
  intro z hz hziso
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hz
  rw [Pi.zero_apply] at hk
  set d : UnitaryField p := star (z k) with hd
  have hd0 : d ≠ 0 := by rw [hd]; exact star_ne_zero.mpr hk
  set w₁ : Fin n → UnitaryField p := Pi.single k d⁻¹ with hw1
  have hzw1 : star z ⬝ᵥ w₁ = 1 := by
    rw [hw1, dotProduct_single, Pi.star_apply, ← hd, mul_inv_cancel₀ hd0]
  have hw1z : star w₁ ⬝ᵥ z = 1 := by rw [dotProduct_star_swap, hzw1, star_one]
  have hw1w1 : star w₁ ⬝ᵥ w₁ = d⁻¹ * star d⁻¹ := by
    rw [hw1, ← Pi.single_star, single_dotProduct, Pi.single_eq_same, mul_comm]
  obtain ⟨t, ht⟩ := UnitaryField.exists_add_star_eq_neg_norm p d⁻¹
  refine ⟨w₁ + t • z, ?_, ?_⟩
  · have hss : star (w₁ + t • z) = star w₁ + star t • star z := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_add, star_mul']
    rw [hss]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hw1w1, hziso, hzw1, hw1z, mul_zero, mul_one, add_zero]
    linear_combination ht
  · rw [dotProduct_add, dotProduct_smul, hzw1, hziso, smul_eq_mul, mul_zero, add_zero]

/-- **Connectivity, the perpendicular case — MACHINE-CHECKED** (formerly the last PSU-faithfulness
axiom). For nonzero isotropic `z₁, z₂` with `⟨z₂,z₁⟩ = 0`, `n ≥ 3`, there is a common
non-orthogonal isotropic `u`. Take a hyperbolic partner `w₁` of `z₁` (`⟨z₁,w₁⟩ = 1`, `w₁`
isotropic). If `⟨z₂,w₁⟩ ≠ 0`, then `u = w₁` works. Otherwise `z₂ ⊥ z₁` **and** `z₂ ⊥ w₁`, i.e.
`z₂ ∈ H^⊥` for the hyperbolic plane `H = ⟨z₁,w₁⟩`. The key trick that avoids any orthogonal-
complement machinery: take *any* hyperbolic partner `w₂` of `z₂` (`⟨z₂,w₂⟩ = 1`), project it into
`H^⊥` as `w₂' = w₂ - α·z₁ - β·w₁` (`α = ⟨w₁,w₂⟩`, `β = ⟨z₁,w₂⟩`), then re-isotropize. The
projected self-product is `⟨w₂',w₂'⟩ = -(α·star β + β·star α)`, which is **automatically** of the
form `-(x + star x)` with `x = α·star β`, so `w₂'' = w₂' + (α·star β)·z₂` is isotropic with the
*explicit* scalar — no trace-surjectivity lemma needed. Then `u = w₁ + w₂'' = w₁ + w₂ - α·z₁ -
β·w₁ + (α·star β)·z₂` is isotropic (it lives in `H ⊕ H^⊥`), with `⟨z₁,u⟩ = 1` and `⟨z₂,u⟩ = 1`.
For `n = 3` the perpendicular sub-case is vacuous (`H^⊥` anisotropic), but the proof is uniform in
`n` and does not rely on that. Discharged 2026-06-04. The non-perpendicular case is in
`exists_common_nonorth_isotropic` below. -/
theorem common_nonorth_isotropic_perp (hn : 3 ≤ n) :
    ∀ z₁ z₂ : Fin n → UnitaryField p, z₁ ≠ 0 → z₂ ≠ 0 →
      star z₁ ⬝ᵥ z₁ = 0 → star z₂ ⬝ᵥ z₂ = 0 → star z₂ ⬝ᵥ z₁ = 0 →
      ∃ u : Fin n → UnitaryField p, u ≠ 0 ∧ star u ⬝ᵥ u = 0 ∧
        star z₁ ⬝ᵥ u ≠ 0 ∧ star z₂ ⬝ᵥ u ≠ 0 := by
  intro z₁ z₂ h1 h2 h1iso h2iso hperp
  obtain ⟨w₁, hw1iso, hzw1⟩ := exists_hyperbolic_partner p hn z₁ h1 h1iso
  have hw1z : star w₁ ⬝ᵥ z₁ = 1 := by rw [dotProduct_star_swap, hzw1, star_one]
  rcases eq_or_ne (star z₂ ⬝ᵥ w₁) 0 with hc1 | hc1
  · -- genuine perpendicular case: `z₂ ⊥ z₁` and `z₂ ⊥ w₁`
    obtain ⟨w₂, hw2iso, hzw2⟩ := exists_hyperbolic_partner p hn z₂ h2 h2iso
    set α : UnitaryField p := star w₁ ⬝ᵥ w₂ with hα
    set β : UnitaryField p := star z₁ ⬝ᵥ w₂ with hβ
    set t : UnitaryField p := α * star β with ht
    -- the off-diagonal inner products of the basis `{w₁, w₂, z₁, z₂}` not already in context
    have hAw1z2 : star w₁ ⬝ᵥ z₂ = 0 := by rw [dotProduct_star_swap, hc1, star_zero]
    have hAw2w1 : star w₂ ⬝ᵥ w₁ = star α := by rw [dotProduct_star_swap, ← hα]
    have hAw2z1 : star w₂ ⬝ᵥ z₁ = star β := by rw [dotProduct_star_swap, ← hβ]
    have hAw2z2 : star w₂ ⬝ᵥ z₂ = 1 := by rw [dotProduct_star_swap, hzw2, star_one]
    have hAz1z2 : star z₁ ⬝ᵥ z₂ = 0 := by rw [dotProduct_star_swap, hperp, star_zero]
    have hstart : star t = β * star α := by rw [ht, star_mul', star_star, mul_comm]
    set u : Fin n → UnitaryField p := w₁ + w₂ - α • z₁ - β • w₁ + t • z₂ with hu
    have hstar : star u =
        star w₁ + star w₂ - star α • star z₁ - star β • star w₁ + star t • star z₂ := by
      rw [hu]; funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
        star_add, star_sub, star_mul', mul_comm]
    have hz1u : star z₁ ⬝ᵥ u = 1 := by
      rw [hu]
      simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hzw1, h1iso,
        hAz1z2, ← hβ]
      ring
    have hz2u : star z₂ ⬝ᵥ u = 1 := by
      rw [hu]
      simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hc1, hzw2, hperp,
        h2iso]
      ring
    refine ⟨u, ?_, ?_, ?_, ?_⟩
    · intro h0
      rw [h0, dotProduct_zero] at hz2u
      exact one_ne_zero hz2u.symm
    · rw [hstar, hu]
      simp only [add_dotProduct, sub_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, hw1iso, hw2iso, hw1z, hzw1, h1iso, h2iso, hzw2,
        hAw1z2, hAw2w1, hAw2z1, hAw2z2, hAz1z2, hc1, hperp, ← hα, ← hβ]
      rw [ht, hstart]
      ring
    · rw [hz1u]; exact one_ne_zero
    · rw [hz2u]; exact one_ne_zero
  · -- `⟨z₂,w₁⟩ ≠ 0`: `u = w₁` is a common non-orthogonal isotropic
    refine ⟨w₁, ?_, hw1iso, ?_, hc1⟩
    · intro h0; rw [h0, dotProduct_zero] at hzw1; exact one_ne_zero hzw1.symm
    · rw [hzw1]; exact one_ne_zero

/-- **Diameter-2 connectivity of the isotropic non-orthogonality graph** (`n ≥ 3`). Any two nonzero
isotropic `z₁, z₂` have a common non-orthogonal isotropic `u`. The non-perpendicular case
(`⟨z₂,z₁⟩ ≠ 0`) is machine-checked here: with a hyperbolic partner `w₁` of `z₁`, either `u = w₁`
(if `⟨z₂,w₁⟩ ≠ 0`) or `u = w₁ + c·z₁` for a trace-zero `c ≠ 0` (then `⟨u,u⟩ = c + star c = 0`,
`⟨z₁,u⟩ = 1`, `⟨z₂,u⟩ = c·⟨z₂,z₁⟩ ≠ 0`). The perpendicular case delegates to
`common_nonorth_isotropic_perp`. -/
theorem exists_common_nonorth_isotropic (hn : 3 ≤ n) :
    ∀ z₁ z₂ : Fin n → UnitaryField p, z₁ ≠ 0 → z₂ ≠ 0 →
      star z₁ ⬝ᵥ z₁ = 0 → star z₂ ⬝ᵥ z₂ = 0 →
      ∃ u : Fin n → UnitaryField p, u ≠ 0 ∧ star u ⬝ᵥ u = 0 ∧
        star z₁ ⬝ᵥ u ≠ 0 ∧ star z₂ ⬝ᵥ u ≠ 0 := by
  intro z₁ z₂ h1 h2 h1iso h2iso
  rcases eq_or_ne (star z₂ ⬝ᵥ z₁) 0 with hperp | hnp
  · exact common_nonorth_isotropic_perp p hn z₁ z₂ h1 h2 h1iso h2iso hperp
  · obtain ⟨w₁, hw1iso, hzw1⟩ := exists_hyperbolic_partner p hn z₁ h1 h1iso
    have hw1z : star w₁ ⬝ᵥ z₁ = 1 := by rw [dotProduct_star_swap, hzw1, star_one]
    rcases eq_or_ne (star z₂ ⬝ᵥ w₁) 0 with hc1 | hc1
    · -- `z₂ ⊥ w₁` but `⟨z₂,z₁⟩ ≠ 0`: use `u = w₁ + c·z₁`, `c` trace-zero `≠ 0`
      obtain ⟨c, hc0, hctr⟩ := UnitaryField.exists_traceZero_ne_zero p
      refine ⟨w₁ + c • z₁, ?_, ?_, ?_, ?_⟩
      · intro h0
        have hz : star z₁ ⬝ᵥ (w₁ + c • z₁) = 0 := by rw [h0, dotProduct_zero]
        rw [dotProduct_add, dotProduct_smul, hzw1, h1iso, smul_eq_mul, mul_zero, add_zero] at hz
        exact one_ne_zero hz
      · have hss : star (w₁ + c • z₁) = star w₁ + star c • star z₁ := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_add, star_mul']
        rw [hss]
        simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          hw1iso, h1iso, hzw1, hw1z, mul_zero, mul_one, add_zero, zero_add]
        linear_combination hctr
      · rw [dotProduct_add, dotProduct_smul, hzw1, h1iso, smul_eq_mul, mul_zero, add_zero]
        exact one_ne_zero
      · rw [dotProduct_add, dotProduct_smul, hc1, smul_eq_mul, zero_add]
        exact mul_ne_zero hc0 hnp
    · -- `⟨z₂,w₁⟩ ≠ 0`: `u = w₁`
      refine ⟨w₁, ?_, hw1iso, ?_, hc1⟩
      · intro h0; rw [h0, dotProduct_zero] at hzw1; exact one_ne_zero hzw1.symm
      · rw [hzw1]; exact one_ne_zero

/-- **Isotropic vectors span** (`n ≥ 3`, machine-checked). For each `i` pick `j ≠ i`; with two
distinct `c, c'` of norm `-1` (`exists_two_norm_neg_one`), `eᵢ + c·eⱼ` and `eᵢ + c'·eⱼ` are
isotropic (`isotropic_single_pair`), their difference gives `eⱼ ∈ span`, hence `eᵢ ∈ span`. As
every standard basis vector lies in the span, the isotropic vectors span `(F_{p²})ⁿ`. -/
theorem isotropic_span (hn : 3 ≤ n) :
    Submodule.span (UnitaryField p) {z : Fin n → UnitaryField p | star z ⬝ᵥ z = 0} = ⊤ := by
  set S := Submodule.span (UnitaryField p) {z : Fin n → UnitaryField p | star z ⬝ᵥ z = 0} with hS
  haveI : Nontrivial (Fin n) := by rw [Fin.nontrivial_iff_two_le]; omega
  obtain ⟨c, c', hcc', hc, hc'⟩ := UnitaryField.exists_two_norm_neg_one p
  -- `a • eₖ = eₖ·a` (scaling a basis vector rescales its value)
  have smul_single : ∀ (a : UnitaryField p) (k : Fin n),
      a • (Pi.single k 1 : Fin n → UnitaryField p) = Pi.single k a := by
    intro a k
    funext m
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  -- every basis vector lies in `S`
  have hsingle : ∀ i : Fin n, (Pi.single i 1 : Fin n → UnitaryField p) ∈ S := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    have hv1 : (Pi.single i 1 + Pi.single j c : Fin n → UnitaryField p) ∈ S :=
      Submodule.subset_span (isotropic_single_pair hji.symm hc)
    have hv2 : (Pi.single i 1 + Pi.single j c' : Fin n → UnitaryField p) ∈ S :=
      Submodule.subset_span (isotropic_single_pair hji.symm hc')
    have hdiff : (Pi.single j (c - c') : Fin n → UnitaryField p) ∈ S := by
      have he : (Pi.single j (c - c') : Fin n → UnitaryField p)
          = (Pi.single i 1 + Pi.single j c) - (Pi.single i 1 + Pi.single j c') := by
        rw [Pi.single_sub]; abel
      rw [he]; exact S.sub_mem hv1 hv2
    have hcc0 : c - c' ≠ 0 := sub_ne_zero.mpr hcc'
    have hsj : (Pi.single j 1 : Fin n → UnitaryField p) ∈ S := by
      have he : (Pi.single j 1 : Fin n → UnitaryField p)
          = (c - c')⁻¹ • (Pi.single j (c - c') : Fin n → UnitaryField p) := by
        rw [← smul_single (c - c') j, smul_smul, inv_mul_cancel₀ hcc0, one_smul]
      rw [he]; exact S.smul_mem _ hdiff
    have he : (Pi.single i 1 : Fin n → UnitaryField p)
        = (Pi.single i 1 + Pi.single j c) - c • (Pi.single j 1 : Fin n → UnitaryField p) := by
      rw [smul_single c j]; abel
    rw [he]; exact S.sub_mem hv1 (S.smul_mem _ hsj)
  -- hence everything lies in `S`
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_single (x i) i]
  exact S.smul_mem _ (hsingle i)

/-- **The center of `SU_n(F_{p²})` consists of scalar matrices** (`n ≥ 3`). A central element fixes
every isotropic line (`su_central_fixes_isotropic_line`, using a nonzero trace-zero scalar), so by
the geometric crux `su_fixes_isotropic_imp_scalar` it is `μ • 1`. This is the algebraic heart of
the faithfulness of the `PSU = SU/Z` action; combined with the (easy) converse it pins
`center = scalars`. -/
theorem su_center_le_scalar (hn : 3 ≤ n)
    (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
    (hg : g ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))) :
    ∃ μ : UnitaryField p, (g : Matrix (Fin n) (Fin n) (UnitaryField p)) = μ • 1 := by
  obtain ⟨a, ha0, ha⟩ := UnitaryField.exists_traceZero_ne_zero p
  refine su_fixes_isotropic_imp_scalar (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) ?_
    (exists_hyperbolic_partner p hn) (exists_common_nonorth_isotropic p hn) (isotropic_span p hn)
    ⟨a, ha0, ha⟩ (UnitaryField.exists_isotropic p n (by omega))
  intro z hziso
  rcases eq_or_ne z 0 with h0 | h0
  · exact ⟨1, by subst h0; simp⟩
  · exact su_central_fixes_isotropic_line g hg h0 hziso a ha0 ha

/-- **`g ∈ SU` fixing every isotropic line is central** (`n ≥ 3`) — the `ker ⊆ center` half of
faithfulness for the `PSU = SU/Z` action on isotropic points. Immediate from the geometric crux
(`g` is scalar) and `su_scalar_mem_center`. -/
theorem su_fixes_isotropic_imp_central (hn : 3 ≤ n)
    (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
    (hfix : ∀ z : Fin n → UnitaryField p, star z ⬝ᵥ z = 0 →
      ∃ l : UnitaryField p, (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ z = l • z) :
    g ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) := by
  obtain ⟨a, ha0, ha⟩ := UnitaryField.exists_traceZero_ne_zero p
  obtain ⟨μ, hμ⟩ := su_fixes_isotropic_imp_scalar
    (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) hfix (exists_hyperbolic_partner p hn)
    (exists_common_nonorth_isotropic p hn) (isotropic_span p hn) ⟨a, ha0, ha⟩
    (UnitaryField.exists_isotropic p n (by omega))
  exact su_scalar_mem_center hμ

/-- **`g ∈ SU` is central iff it is a scalar matrix** (`n ≥ 3`). The center characterization
underlying the faithfulness of `PSU = SU/Z`. -/
theorem su_mem_center_iff_scalar (hn : 3 ≤ n)
    (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) :
    g ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) ↔
      ∃ μ : UnitaryField p, (g : Matrix (Fin n) (Fin n) (UnitaryField p)) = μ • 1 :=
  ⟨su_center_le_scalar p hn g, fun ⟨_, hμ⟩ => su_scalar_mem_center hμ⟩

/-- **`PSU_n(F_{p²}) = SU/Z` is nontrivial** (`n ≥ 3`) — the Iwasawa `Nontrivial` obligation. A
transvection `τ_{v,a}` (`v` isotropic `≠ 0`, `a` trace-zero `≠ 0`) is non-central: were it central
it would be a scalar `μ • 1` (`su_center_le_scalar`), but its off-diagonal `(i,k)` entries
`a·vᵢ·star(v_k)` then vanish, forcing `v` supported at a single coordinate `k` — impossible for an
isotropic vector (`⟨v,v⟩ = N(v_k) ≠ 0`). -/
theorem PSU_nontrivial (hn : 3 ≤ n) : Nontrivial (PSUConcrete n p) := by
  obtain ⟨v, hv, hiso⟩ := UnitaryField.exists_isotropic p n (by omega)
  obtain ⟨a, ha0, ha⟩ := UnitaryField.exists_traceZero_ne_zero p
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  rw [Pi.zero_apply] at hk
  refine ⟨QuotientGroup.mk (uTransvecSU v a hiso ha), 1, ?_⟩
  rw [Ne, QuotientGroup.eq_one_iff]
  intro hmem
  obtain ⟨μ, hμ⟩ := su_center_le_scalar p hn _ hmem
  rw [uTransvecSU_coe] at hμ
  have hsk : (star v) k ≠ 0 := by rw [Pi.star_apply]; exact star_ne_zero.mpr hk
  -- off-diagonal entries vanish ⟹ `v` is supported only at `k`
  have hvi : ∀ i, i ≠ k → v i = 0 := by
    intro i hik
    have hentry := congr_fun₂ hμ i k
    rw [uTransvection, Matrix.add_apply, Matrix.one_apply_ne hik, Matrix.smul_apply,
      vecMulVec_apply, Matrix.smul_apply, Matrix.one_apply_ne hik, smul_zero, smul_eq_mul,
      zero_add] at hentry
    rcases mul_eq_zero.mp hentry with h | h
    · exact absurd h ha0
    · exact (mul_eq_zero.mp h).resolve_right hsk
  -- then `⟨v,v⟩ = star(v_k)·v_k`, which is nonzero — contradicting isotropy
  have hsum : star v ⬝ᵥ v = star (v k) * v k := by
    rw [dotProduct, Finset.sum_eq_single k (fun i _ hik => by rw [hvi i hik, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.star_apply]
  rw [hsum] at hiso
  exact hk ((mul_eq_zero.mp hiso).resolve_left (by rwa [Pi.star_apply] at hsk))

end Concrete

end FiniteSimpleGroups.PSU

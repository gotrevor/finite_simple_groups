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

/-! ### Perp-projection infrastructure for the generation induction (`hgen`)

The Dieudonné/Eichler proof that the isotropic unitary transvections generate `SU` reduces a
general `g ∈ SU`, via transvection/Eichler transitivity, to one **fixing an isotropic hyperbolic
pair `(e,f)` pointwise** (`⟨e,f⟩ = 1`, `e,f` isotropic); such a `g` restricts to `SU` on the
orthogonal complement `⟨e,f⟩^⊥`, where transvections generate by the dimension induction and extend
back (centres in `⟨e,f⟩^⊥`, fixing `e,f` — `uTransvection_fixes_pair`). These are the structural
bricks of the complement decomposition `V = ⟨e,f⟩ ⊕ ⟨e,f⟩^⊥`, unitary analogues of the symplectic
`perpComp` / `perp_form_ne_of_mem_perp` development. The Hermitian form `⟨x,y⟩ = star x ⬝ᵥ y` is
conjugate-linear in the first slot, handled via `dotProduct_star_swap`. -/

/-- **The Hermitian form is nondegenerate**: if `⟨u,v⟩ = star u ⬝ᵥ v = 0` for every `v`, then
`u = 0`. Testing against `eᵢ` gives `star (uᵢ) = 0`, hence `uᵢ = 0`. -/
theorem uForm_nondegenerate {u : n → F} (h : ∀ v, star u ⬝ᵥ v = 0) : u = 0 := by
  funext i
  have hi := h (Pi.single i 1)
  rw [dotProduct_single, mul_one, Pi.star_apply, star_eq_zero] at hi
  rw [Pi.zero_apply]; exact hi

/-- **Explicit projection onto `⟨e,f⟩^⊥`** for an isotropic hyperbolic pair `(e,f)`:
`uPerpComp e f x = x − ⟨f,x⟩·e − ⟨e,x⟩·f`. A closed formula on the coordinate space — no abstract
submodule machinery — the foundation of the generation-induction complement decomposition. -/
noncomputable def uPerpComp (e f x : n → F) : n → F :=
  x - (star f ⬝ᵥ x) • e - (star e ⬝ᵥ x) • f

omit [DecidableEq n] in
/-- `uPerpComp e f x` lands in `⟨e,f⟩^⊥`: `⟨e, uPerpComp e f x⟩ = ⟨f, uPerpComp e f x⟩ = 0`
(for `e,f` isotropic with `⟨e,f⟩ = 1`). The defining property of the complement projection. -/
theorem uPerpComp_mem_perp {e f : n → F} (hef : star e ⬝ᵥ f = 1)
    (hee : star e ⬝ᵥ e = 0) (hff : star f ⬝ᵥ f = 0) (x : n → F) :
    star e ⬝ᵥ uPerpComp e f x = 0 ∧ star f ⬝ᵥ uPerpComp e f x = 0 := by
  have hfe : star f ⬝ᵥ e = 1 := by rw [dotProduct_star_swap, hef, star_one]
  refine ⟨?_, ?_⟩
  · simp only [uPerpComp, dotProduct_sub, dotProduct_smul, smul_eq_mul, hee, hef, mul_zero, mul_one]
    ring
  · simp only [uPerpComp, dotProduct_sub, dotProduct_smul, smul_eq_mul, hff, hfe, mul_zero, mul_one]
    ring

omit [DecidableEq n] in
/-- The complement projection recovers `x` modulo `⟨e,f⟩`: `x = uPerpComp e f x + ⟨f,x⟩·e
+ ⟨e,x⟩·f`. The `V = ⟨e,f⟩ ⊕ ⟨e,f⟩^⊥` decomposition, witnessed concretely. -/
theorem uPerpComp_add_span (e f x : n → F) :
    x = uPerpComp e f x + (star f ⬝ᵥ x) • e + (star e ⬝ᵥ x) • f := by
  simp only [uPerpComp]; abel

/-- **`⟨·,·⟩` restricts non-degenerately to `⟨e,f⟩^⊥`**: for `u ∈ ⟨e,f⟩^⊥` non-zero there is a
`z ∈ ⟨e,f⟩^⊥` with `⟨u,z⟩ ≠ 0`. Were `⟨u,·⟩` zero on all of `⟨e,f⟩^⊥`, then — since `u ∈ ⟨e,f⟩^⊥`
makes `⟨u,e⟩ = ⟨u,f⟩ = 0` too (`dotProduct_star_swap`) and `V = ⟨e,f⟩ ⊕ ⟨e,f⟩^⊥`
(`uPerpComp_add_span`) — `⟨u,·⟩` would vanish on all of `V`, forcing `u = 0`
(`uForm_nondegenerate`). The relative non-degeneracy powering transitivity within the complement. -/
theorem uPerp_form_ne_of_mem_perp {e f : n → F} (hef : star e ⬝ᵥ f = 1)
    (hee : star e ⬝ᵥ e = 0) (hff : star f ⬝ᵥ f = 0)
    {u : n → F} (hue : star e ⬝ᵥ u = 0) (huf : star f ⬝ᵥ u = 0) (hu : u ≠ 0) :
    ∃ z, star e ⬝ᵥ z = 0 ∧ star f ⬝ᵥ z = 0 ∧ star u ⬝ᵥ z ≠ 0 := by
  by_contra hcon
  apply hu
  apply uForm_nondegenerate
  intro x
  have hue' : star u ⬝ᵥ e = 0 := by rw [dotProduct_star_swap, hue, star_zero]
  have huf' : star u ⬝ᵥ f = 0 := by rw [dotProduct_star_swap, huf, star_zero]
  have hperp := uPerpComp_mem_perp hef hee hff x
  have hz : star u ⬝ᵥ uPerpComp e f x = 0 := by
    by_contra hne
    exact hcon ⟨uPerpComp e f x, hperp.1, hperp.2, hne⟩
  rw [uPerpComp_add_span e f x, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, hz, hue', huf']
  ring

/-- **Relative `exists_form_both_ne` within `⟨e,f⟩^⊥`**: for `u, w ∈ ⟨e,f⟩^⊥` non-zero there is a
`z ∈ ⟨e,f⟩^⊥` simultaneously non-orthogonal to both. Standard-witness combination `z₁, z₂, z₁+z₂`
from the relative non-degeneracy `uPerp_form_ne_of_mem_perp`. The transitivity-within-complement
input for the generation induction. -/
theorem exists_uPerp_form_both_ne {e f : n → F} (hef : star e ⬝ᵥ f = 1)
    (hee : star e ⬝ᵥ e = 0) (hff : star f ⬝ᵥ f = 0)
    {u w : n → F} (hue : star e ⬝ᵥ u = 0) (huf : star f ⬝ᵥ u = 0) (hu : u ≠ 0)
    (hwe : star e ⬝ᵥ w = 0) (hwf : star f ⬝ᵥ w = 0) (hw : w ≠ 0) :
    ∃ z, (star e ⬝ᵥ z = 0 ∧ star f ⬝ᵥ z = 0) ∧ star u ⬝ᵥ z ≠ 0 ∧ star w ⬝ᵥ z ≠ 0 := by
  obtain ⟨z₁, hz1e, hz1f, hz1⟩ := uPerp_form_ne_of_mem_perp hef hee hff hue huf hu
  obtain ⟨z₂, hz2e, hz2f, hz2⟩ := uPerp_form_ne_of_mem_perp hef hee hff hwe hwf hw
  by_cases hwz1 : star w ⬝ᵥ z₁ = 0
  · by_cases huz2 : star u ⬝ᵥ z₂ = 0
    · refine ⟨z₁ + z₂,
        ⟨by rw [dotProduct_add, hz1e, hz2e, add_zero],
          by rw [dotProduct_add, hz1f, hz2f, add_zero]⟩, ?_, ?_⟩
      · rw [dotProduct_add, huz2, add_zero]; exact hz1
      · rw [dotProduct_add, hwz1, zero_add]; exact hz2
    · exact ⟨z₂, ⟨hz2e, hz2f⟩, huz2, hz2⟩
  · exact ⟨z₁, ⟨hz1e, hz1f⟩, hz1, hwz1⟩

/-! ### Determinant base case of the generation induction

The terminal step of the Dieudonné dimension induction: a special-unitary `g` (`star g * g = 1`,
`det g = 1`) fixing every standard basis vector but one is the identity. The `k`-th column is
orthogonal to the fixed `eᵢ` (`i ≠ k`), forcing it to `(c_k)_k • eₖ`; the determinant equals
`(c_k)_k` (all other columns standard), and `det g = 1` pins it to `eₖ`. This is the unitary
analogue of the symplectic `sp_eq_one_of_FixS_univ` (refined by the `det` for the lone anisotropic
coordinate of odd-dimensional unitary spaces). Discharged by Aristotle (project
`c861683e`), re-verified axiom-clean in-kernel. -/

set_option maxHeartbeats 800000 in
/-- The columns of a unitary matrix are orthonormal for the standard Hermitian form:
`⟨g·x, g·y⟩ = ⟨x,y⟩`, from `star g * g = 1`. (Variant of `u_preserves_form` with the explicit
unitarity equation as hypothesis.) -/
theorem u_preserves_form' {g : Matrix n n F} (hg : star g * g = 1) (x y : n → F) :
    star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y := by
  convert congr_arg (fun m => star x ⬝ᵥ m *ᵥ y) hg using 1
  · simp +decide [Matrix.dotProduct_mulVec]
    congr! 1
    ext i; simp +decide [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    simp +decide [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm]
    exact Finset.sum_comm
  · simp +decide

set_option maxHeartbeats 1600000 in
/-- **Determinant base case.** A special-unitary matrix (`star g * g = 1`, `det g = 1`) fixing every
standard basis vector but one is the identity. Terminal case of the `SU` generation induction. -/
theorem u_eq_one_of_fixes_all_but_one {g : Matrix n n F}
    (hu : star g * g = 1) (hdet : g.det = 1) {k : n}
    (hfix : ∀ i, i ≠ k → g *ᵥ Pi.single i 1 = Pi.single i 1) :
    g = 1 := by
  have hc : g *ᵥ (Pi.single k 1 : n → F)
      = (g *ᵥ (Pi.single k 1 : n → F)) k • (Pi.single k 1 : n → F) := by
    have hc : ∀ i ≠ k, (g *ᵥ (Pi.single k 1 : n → F)) i = 0 := by
      intro i hi
      have := u_preserves_form' hu (Pi.single i 1) (Pi.single k 1)
      simp_all +decide [dotProduct]
      simp_all +decide [Pi.single_apply]
      rw [Finset.sum_eq_single i] at this <;> aesop
    ext i; by_cases hi : i = k <;> simp +decide [*]
  have hdet_eq : (g *ᵥ (Pi.single k 1 : n → F)) k = g.det := by
    have hdet_eq : g = Matrix.updateCol (1 : Matrix n n F) k (g *ᵥ (Pi.single k 1 : n → F)) := by
      ext i j; by_cases hij : j = k <;> simp +decide [hij]
      specialize hfix j hij; replace hfix := congr_fun hfix i
      simp_all +singlePass [Matrix.mulVec, dotProduct]
      simp_all +decide [Pi.single_apply, Matrix.one_apply]
    conv_rhs => rw [hdet_eq]
    rw [Matrix.det_apply']
    rw [Finset.sum_eq_single (Equiv.refl n)] <;>
      simp +contextual [Matrix.one_apply, Matrix.updateCol_apply]
    intro b hb
    by_cases hbk : b k = k
    · rw [Finset.prod_eq_zero_iff.mpr]
      · exact Or.inr rfl
      · grind +qlia
    · rw [Finset.prod_eq_zero (Finset.mem_univ (b k))] <;> simp +decide [hbk]
  rw [hdet_eq, hdet] at hc
  ext i j; by_cases hij : j = k <;> simp_all +decide [Matrix.mulVec, funext_iff]
  · by_cases hi : i = k <;> aesop
  · by_cases hi : i = j <;> aesop

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

/-- **Explicit coordinate hyperbolic pair** for the identity Hermitian form. For distinct
coordinates `i ≠ j` and `2 ≠ 0`, the isotropic vectors `a = eᵢ + c·eⱼ` (`N(c) = −1`) and
`b = 2⁻¹·(eᵢ − c·eⱼ)` form a hyperbolic pair (`⟨a,b⟩ = 1`), supported on `{i,j}`. The cross term
`⟨a, eᵢ − c·eⱼ⟩ = 1 − N(c) = 2`; the `2⁻¹` rescales it to `1`. The building block of the isotropic
hyperbolic basis underlying the `hgen` generation dimension induction (coordinate-pairs
`(2i, 2i+1)` tile the even part; a lone anisotropic `eₙ` remains for odd `n`). -/
theorem exists_coord_hyperbolic_pair (h2 : (2 : UnitaryField p) ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    ∃ a b : Fin n → UnitaryField p,
      star a ⬝ᵥ a = 0 ∧ star b ⬝ᵥ b = 0 ∧ star a ⬝ᵥ b = 1 := by
  obtain ⟨c, hc⟩ := UnitaryField.exists_norm_neg_one p
  have hcn : (-c) * star (-c) = -1 := by rw [star_neg, neg_mul_neg]; exact hc
  -- cross term ⟨eᵢ + c·eⱼ, eᵢ + (-c)·eⱼ⟩ = 2
  have hcross : star ((Pi.single i 1 : Fin n → UnitaryField p) + Pi.single j c) ⬝ᵥ
      ((Pi.single i 1 : Fin n → UnitaryField p) + Pi.single j (-c)) = 2 := by
    rw [star_add, ← Pi.single_star, ← Pi.single_star, star_one]
    simp only [add_dotProduct, dotProduct_add, single_dotProduct, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, mul_one, mul_zero, add_zero, zero_add,
      mul_neg]
    rw [mul_comm (star c) c, hc]; ring
  refine ⟨Pi.single i 1 + Pi.single j c,
    (2⁻¹ : UnitaryField p) • (Pi.single i 1 + Pi.single j (-c)),
    isotropic_single_pair hij hc, ?_, ?_⟩
  · rw [star_smul, smul_dotProduct, dotProduct_smul, isotropic_single_pair hij hcn,
      smul_zero, smul_zero]
  · rw [dotProduct_smul, hcross, smul_eq_mul, inv_mul_cancel₀ h2]

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

/-- **Isotropic separation, given a perpendicular partner — MACHINE-CHECKED.** If `x, y` are
isotropic with `⟨x,y⟩ = 0` and there is an isotropic `v` with `⟨x,v⟩ = 1` and `⟨y,v⟩ = 0` (a
hyperbolic partner of `x` lying in `y^⊥`), then there is an isotropic `s` with `⟨x,s⟩ = 0` and
`⟨y,s⟩ ≠ 0`. Explicit witness: with `w` a hyperbolic partner of `y` (`⟨y,w⟩ = 1`), `α = ⟨x,w⟩` and
`γ = α·⟨w,v⟩`, the vector `s = w - α·v + γ·y` is isotropic (the choice `γ = α·⟨w,v⟩` makes the
self-product trace `-(αω + star(αω)) + (γ + star γ)` cancel), with `⟨x,s⟩ = 0` and `⟨y,s⟩ = 1`. This
discharges ALL of the separation's algebra; the only input it consumes beyond the standard
hyperbolic-partner lemma is the perpendicular partner `v` — the unitary Witt-extension atom (`∃`
isotropic partner of `x` inside `y^⊥`). For `n ≥ 4`; vacuous for `n = 3`. -/
theorem exists_isotropic_perp_nonperp_of_perp_partner (hn : 3 ≤ n)
    {x y v : Fin n → UnitaryField p}
    (hyiso : star y ⬝ᵥ y = 0) (hy0 : y ≠ 0)
    (hperp : star x ⬝ᵥ y = 0)
    (hviso : star v ⬝ᵥ v = 0) (hxv : star x ⬝ᵥ v = 1) (hyv : star y ⬝ᵥ v = 0) :
    ∃ s : Fin n → UnitaryField p, s ≠ 0 ∧ star s ⬝ᵥ s = 0 ∧
      star x ⬝ᵥ s = 0 ∧ star y ⬝ᵥ s ≠ 0 := by
  obtain ⟨w, hwiso, hyw⟩ := exists_hyperbolic_partner p hn y hy0 hyiso
  have hwy : star w ⬝ᵥ y = 1 := by rw [dotProduct_star_swap, hyw, star_one]
  have hvy : star v ⬝ᵥ y = 0 := by rw [dotProduct_star_swap, hyv, star_zero]
  set α : UnitaryField p := star x ⬝ᵥ w with hα
  set ω : UnitaryField p := star w ⬝ᵥ v with hω
  set γ : UnitaryField p := α * ω with hγ
  set s : Fin n → UnitaryField p := w - α • v + γ • y with hs
  have hxs : star x ⬝ᵥ s = 0 := by
    rw [hs]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hxv, hperp, ← hα,
      mul_one, mul_zero, add_zero, sub_self]
  have hys : star y ⬝ᵥ s = 1 := by
    rw [hs]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hyw, hyv, hyiso,
      mul_zero, sub_zero, add_zero]
  refine ⟨s, ?_, ?_, hxs, ?_⟩
  · intro h0; rw [h0, dotProduct_zero] at hys; exact one_ne_zero hys.symm
  · have hvw : star v ⬝ᵥ w = star ω := by rw [hω, dotProduct_star_swap]
    have hstar : star s = star w - star α • star v + star γ • star y := by
      rw [hs]; funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
        star_add, star_sub, star_mul', mul_comm]
    rw [hstar, hs]
    simp only [add_dotProduct, sub_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, hwiso, hviso, hyiso, hwy, hvy, hyw, hyv, ← hω,
      mul_zero, sub_zero, add_zero, mul_one]
    rw [hvw, show star (α * ω) = star α * star ω from star_mul' α ω]
    ring
  · rw [hys]; exact one_ne_zero

/-- **Lemma T — MACHINE-CHECKED.** Every `-(⟨w,w⟩)` is a Hermitian-trace value:
`∃ t, t + star t = -(star w ⬝ᵥ w)`. The self-product `⟨w,w⟩ = Σ N(wⱼ)` is `algebraMap` of a sum of
field norms (a fixed-field element), and the trace `a ↦ a + star a` is surjective onto the fixed
field. Generalizes `UnitaryField.exists_add_star_eq_neg_norm` from one norm to a self-dot-product. -/
theorem exists_add_star_eq_neg_dotProduct_self (w : Fin n → UnitaryField p) :
    ∃ t : UnitaryField p, t + star t = -(star w ⬝ᵥ w) := by
  have hsum : star w ⬝ᵥ w
      = (algebraMap (ZMod p) (UnitaryField p)) (∑ j, Algebra.norm (ZMod p) (w j)) := by
    rw [map_sum, dotProduct]
    exact Finset.sum_congr rfl
      (fun j _ => by rw [algebraMap_norm_eq_mul_star, Pi.star_apply, mul_comm])
  obtain ⟨t, ht⟩ := Algebra.trace_surjective (ZMod p) (UnitaryField p)
    (-(∑ j, Algebra.norm (ZMod p) (w j)))
  exact ⟨t, by rw [← algebraMap_trace_eq_add_star, ht, map_neg, ← hsum]⟩

/-- **Separation, no isotropy needed — MACHINE-CHECKED.** If `x` is not a scalar multiple of `y`
(and `y ≠ 0`), there is a `u` perpendicular to `y` but not to `x`: `⟨y,u⟩ = 0`, `⟨x,u⟩ ≠ 0`. Pure
linear algebra: if no such `u` existed, `⟨x,·⟩` would vanish on `ker ⟨y,·⟩`, forcing
`star x = c·star y`, i.e. `x = star c · y`. -/
theorem exists_perp_nonperp {x y : Fin n → UnitaryField p} (hy0 : y ≠ 0)
    (hnp : ¬ ∃ c : UnitaryField p, x = c • y) :
    ∃ u : Fin n → UnitaryField p, star y ⬝ᵥ u = 0 ∧ star x ⬝ᵥ u ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hnp
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (star_vec_ne_zero hy0)
  rw [Pi.zero_apply] at hk
  set c : UnitaryField p := (star x) k * ((star y) k)⁻¹ with hc
  have hcoord : ∀ j, (star x) j = c * (star y) j := by
    intro j
    have hu : star y ⬝ᵥ ((Pi.single j 1 : Fin n → UnitaryField p)
        - ((star y) j * ((star y) k)⁻¹) • (Pi.single k 1 : Fin n → UnitaryField p)) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, dotProduct_single, dotProduct_single, mul_one, mul_one,
        smul_eq_mul, mul_assoc, inv_mul_cancel₀ hk, mul_one, sub_self]
    have hx := h _ hu
    rw [dotProduct_sub, dotProduct_smul, dotProduct_single, dotProduct_single, mul_one, mul_one,
      smul_eq_mul, sub_eq_zero] at hx
    rw [hc, hx]; ring
  refine ⟨star c, ?_⟩
  have hsx : star x = c • star y :=
    funext fun j => by rw [Pi.smul_apply, smul_eq_mul]; exact hcoord j
  have hxx : x = star (c • star y) := by rw [← hsx, star_star]
  rw [hxx]; funext i
  simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul', star_star]

/-- **Perpendicular partner exists — MACHINE-CHECKED (the discharge of `hPP`).** For `x` nonzero
isotropic and `y` nonzero with `⟨x,y⟩ = 0` and `x ∦ y`, there is an isotropic `v` with `⟨x,v⟩ = 1`,
`⟨y,v⟩ = 0`. This was feared to be a Witt-extension fact; it is **not**. Get `u ⊥ y` with `⟨x,u⟩ ≠ 0`
(`exists_perp_nonperp`), rescale to `w₁ = ⟨x,u⟩⁻¹·u` (so `⟨x,w₁⟩ = 1`, `⟨y,w₁⟩ = 0`, both inside
`y^⊥ ⊇ span{x,u}`), then `v = w₁ + t·x` with `t + star t = -⟨w₁,w₁⟩` (Lemma T). Because
`⟨x,w₁⟩ = 1 ≠ 0` the `x`-correction is *effective* (the trace term appears), so `v` is isotropic; and
`v ∈ span{x,u} ⊆ y^⊥`, so `⟨y,v⟩ = 0`. Discharges the last existence atom of PSU primitivity. -/
theorem exists_isotropic_perp_partner {x y : Fin n → UnitaryField p}
    (hxiso : star x ⬝ᵥ x = 0) (hy0 : y ≠ 0) (hperp : star x ⬝ᵥ y = 0)
    (hnp : ¬ ∃ c : UnitaryField p, x = c • y) :
    ∃ v : Fin n → UnitaryField p, star v ⬝ᵥ v = 0 ∧
      star x ⬝ᵥ v = 1 ∧ star y ⬝ᵥ v = 0 := by
  obtain ⟨u, hyu, hxu⟩ := exists_perp_nonperp p hy0 hnp
  have hyx : star y ⬝ᵥ x = 0 := by rw [dotProduct_star_swap, hperp, star_zero]
  obtain ⟨w₁, hxw1, hyw1⟩ :
      ∃ w₁ : Fin n → UnitaryField p, star x ⬝ᵥ w₁ = 1 ∧ star y ⬝ᵥ w₁ = 0 :=
    ⟨(star x ⬝ᵥ u)⁻¹ • u, by rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hxu],
      by rw [dotProduct_smul, smul_eq_mul, hyu, mul_zero]⟩
  obtain ⟨t, ht⟩ := exists_add_star_eq_neg_dotProduct_self p w₁
  refine ⟨w₁ + t • x, ?_, ?_, ?_⟩
  · have hxw1' : star w₁ ⬝ᵥ x = 1 := by rw [dotProduct_star_swap, hxw1, star_one]
    have hss : star (w₁ + t • x) = star w₁ + star t • star x := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_add, star_mul']
    rw [hss]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hxiso, hxw1, hxw1', mul_one, mul_zero, add_zero]
    linear_combination ht
  · rw [dotProduct_add, hxw1, dotProduct_smul, smul_eq_mul, hxiso, mul_zero, add_zero]
  · rw [dotProduct_add, hyw1, dotProduct_smul, smul_eq_mul, hyx, mul_zero, add_zero]

/-- **Transvection transitivity, non-orthogonal case** (the unitary Witt transitivity core that
needs NO form classification): for nonzero isotropic `v, w` with `⟨v,w⟩ = β ≠ 0`, the element
`g = τ_{v,b}·τ_{w,a} ∈ SU` maps `v` to the nonzero multiple `(a·star β)·w` of `w`. The trick: a
single product of two transvections moves `v` along its orbit to `[w]` —
`τ_{w,a}·v = v + (a·star β)·w`, then `τ_{v,b}` (with `b·a·N(β) = -1`, `a` any nonzero trace-zero,
`b = -(N(β)·a)⁻¹` automatically trace-zero since `N(β)` is fixed) kills the `v`-component. Both
factors are in `SU` (isotropic centres, trace-zero parameters). This is the elementary Eichler
move; no orthogonal-complement decomposition or Hermitian-form equivalence is needed. -/
theorem exists_su_maps_nonorth (v w : Fin n → UnitaryField p)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0)
    (hvw : star v ⬝ᵥ w ≠ 0) :
    ∃ (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (c : UnitaryField p),
      c ≠ 0 ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ v = c • w := by
  have hβ : star w ⬝ᵥ v = star (star v ⬝ᵥ w) := dotProduct_star_swap v w
  set β := star v ⬝ᵥ w with hβdef
  set Nβ := star β * β with hNdef
  have hNβ0 : Nβ ≠ 0 := mul_ne_zero (star_ne_zero.mpr hvw) hvw
  have hNβH : star Nβ = Nβ := by rw [hNdef, star_mul', star_star, mul_comm]
  obtain ⟨t, ht0, httr⟩ := UnitaryField.exists_traceZero_ne_zero p
  have hstart : star t = -t := by linear_combination httr
  set b := -(Nβ⁻¹ * t⁻¹) with hbdef
  have hb_tr : b + star b = 0 := by
    rw [hbdef, star_neg, star_mul', star_inv₀, star_inv₀, hNβH, hstart, inv_neg]
    ring
  have hcoef : b * (t * Nβ) = -1 := by
    rw [hbdef, neg_mul,
      show Nβ⁻¹ * t⁻¹ * (t * Nβ) = (Nβ⁻¹ * Nβ) * (t⁻¹ * t) by ring,
      inv_mul_cancel₀ hNβ0, inv_mul_cancel₀ ht0, mul_one]
  refine ⟨uTransvecSU v b hviso hb_tr * uTransvecSU w t hwiso httr, t * star β,
    mul_ne_zero ht0 (star_ne_zero.mpr hvw), ?_⟩
  rw [Submonoid.coe_mul, uTransvecSU_coe, uTransvecSU_coe, ← Matrix.mulVec_mulVec,
    uTransvection_mulVec w t v, hβ, uTransvection_mulVec v b,
    dotProduct_add, dotProduct_smul, hviso, ← hβdef, smul_eq_mul, zero_add,
    show t * star β * β = t * Nβ by rw [hNdef]; ring, hcoef, neg_one_smul]
  abel

/-- **Two-transvection move that ALSO fixes a vector `x` orthogonal to both centres** (the Eichler
seed for stabilizer-transitivity `hT1`/`hT2`). For isotropic `v, w` with `⟨v,w⟩ ≠ 0`, and any `x`
with `⟨v,x⟩ = 0` and `⟨w,x⟩ = 0`, the element `g = τ_{v,b}·τ_{w,a} ∈ SU` maps `v ↦ c·w` (`c ≠ 0`) AND
fixes `x`. Each transvection acts by `z ↦ z + (·)⟨u,z⟩·u`, so a centre `u ⊥ x` leaves `x` fixed — i.e.
transvections with centres in `x^⊥` lie in `Stab[x]`. Same `g`/`c` as `exists_su_maps_nonorth`. -/
theorem exists_su_fixes_maps_nonorth (v w x : Fin n → UnitaryField p)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0)
    (hvw : star v ⬝ᵥ w ≠ 0) (hvx : star v ⬝ᵥ x = 0) (hwx : star w ⬝ᵥ x = 0) :
    ∃ (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (c : UnitaryField p),
      c ≠ 0 ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ v = c • w ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x = x := by
  have hβ : star w ⬝ᵥ v = star (star v ⬝ᵥ w) := dotProduct_star_swap v w
  set β := star v ⬝ᵥ w with hβdef
  set Nβ := star β * β with hNdef
  have hNβ0 : Nβ ≠ 0 := mul_ne_zero (star_ne_zero.mpr hvw) hvw
  have hNβH : star Nβ = Nβ := by rw [hNdef, star_mul', star_star, mul_comm]
  obtain ⟨t, ht0, httr⟩ := UnitaryField.exists_traceZero_ne_zero p
  have hstart : star t = -t := by linear_combination httr
  set b := -(Nβ⁻¹ * t⁻¹) with hbdef
  have hb_tr : b + star b = 0 := by
    rw [hbdef, star_neg, star_mul', star_inv₀, star_inv₀, hNβH, hstart, inv_neg]
    ring
  have hcoef : b * (t * Nβ) = -1 := by
    rw [hbdef, neg_mul,
      show Nβ⁻¹ * t⁻¹ * (t * Nβ) = (Nβ⁻¹ * Nβ) * (t⁻¹ * t) by ring,
      inv_mul_cancel₀ hNβ0, inv_mul_cancel₀ ht0, mul_one]
  refine ⟨uTransvecSU v b hviso hb_tr * uTransvecSU w t hwiso httr, t * star β,
    mul_ne_zero ht0 (star_ne_zero.mpr hvw), ?_, ?_⟩
  · rw [Submonoid.coe_mul, uTransvecSU_coe, uTransvecSU_coe, ← Matrix.mulVec_mulVec,
      uTransvection_mulVec w t v, hβ, uTransvection_mulVec v b,
      dotProduct_add, dotProduct_smul, hviso, ← hβdef, smul_eq_mul, zero_add,
      show t * star β * β = t * Nβ by rw [hNdef]; ring, hcoef, neg_one_smul]
    abel
  · rw [Submonoid.coe_mul, uTransvecSU_coe, uTransvecSU_coe, ← Matrix.mulVec_mulVec,
      uTransvection_mulVec w t x, hwx, mul_zero, zero_smul, add_zero,
      uTransvection_mulVec v b x, hvx, mul_zero, zero_smul, add_zero]

/-- **`Stab[x]`-transitivity on the isotropic mates of `x` — the Eichler/Siegel discharge of `hT1`**
(vector level, NO Witt theorem). For `x` isotropic and `y, y'` **isotropic** with
`⟨x,y⟩ = ⟨x,y'⟩ = 1` (hyperbolic mates of `x`), there is `g ∈ SU` with `g·x = x` and `g·y = y'`.

Take `g = τ_{x,c} · E_{x,h,μ}` where `h = y'-y` (so `⟨x,h⟩ = 0`), `μ` solves the trace condition
`μ + star μ = ⟨h,h⟩` (`exists_add_star_eq_neg_dotProduct_self`, via `μ = -t`), and
`c = ⟨h,y⟩ + μ`. The Eichler element `E` (a genuine isometry that a *single* unitary transvection
cannot supply) fixes `x` and sends `y ↦ y' - c·x`; the correction scalar `c` is **automatically
trace-zero**, because `y, y'` are isotropic:
`c + star c = ⟨h,y⟩ + ⟨y,h⟩ + ⟨h,h⟩ = 0` after expanding `h = y'-y` with `⟨y,y⟩ = ⟨y',y'⟩ = 0`. Hence
`τ_{x,c} ∈ SU` clears the leftover `c·x`. This is the unitary analogue of the symplectic
`exists_sp_transvecFixing_maps_mate`, the relative-transitivity engine of the line stabiliser. -/
theorem exists_su_fixes_maps_isotropic_mate (x y y' : Fin n → UnitaryField p)
    (hxiso : star x ⬝ᵥ x = 0) (hyiso : star y ⬝ᵥ y = 0) (hy'iso : star y' ⬝ᵥ y' = 0)
    (hxy : star x ⬝ᵥ y = 1) (hxy' : star x ⬝ᵥ y' = 1) :
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p),
      (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x = x ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ y = y' := by
  set h := y' - y with hh_def
  have hxh : star x ⬝ᵥ h = 0 := by rw [hh_def, dotProduct_sub, hxy, hxy', sub_self]
  obtain ⟨t, ht⟩ := exists_add_star_eq_neg_dotProduct_self p h
  set μ := -t with hμ_def
  have hμ : μ + star μ = star h ⬝ᵥ h := by rw [hμ_def, star_neg, ← neg_add, ht, neg_neg]
  set c := star h ⬝ᵥ y + μ with hc_def
  -- the Eichler element fixes `x` and sends `y ↦ y' - c·x`
  have hE_x : uEichler x h μ *ᵥ x = x := uEichler_apply_self x h μ hxiso hxh
  have hyh : y' = y + h := by rw [hh_def]; abel
  have hE_y : uEichler x h μ *ᵥ y = y' - c • x := by
    rw [uEichler_mulVec, hxy, one_smul, mul_one, hc_def, add_smul, hyh]
    abel
  -- the correction scalar `c` is trace-zero (uses isotropy of `y, y'`)
  have hc_tr : c + star c = 0 := by
    have hsc : star c = star y ⬝ᵥ h + star μ := by
      rw [hc_def, star_add]
      exact congrArg (· + star μ) (dotProduct_star_swap h y).symm
    have key : star h ⬝ᵥ y + star y ⬝ᵥ h + star h ⬝ᵥ h = 0 := by
      rw [hh_def]
      simp only [star_sub, sub_dotProduct, dotProduct_sub, hyiso, hy'iso]
      ring
    rw [hc_def, hsc]; linear_combination key + hμ
  -- assemble `g = τ_{x,c} · E`
  have hEcoe : ((⟨uEichler x h μ, uEichler_mem_su x h μ hxiso hxh hμ⟩ :
      Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) :
      Matrix (Fin n) (Fin n) (UnitaryField p)) = uEichler x h μ := rfl
  refine ⟨uTransvecSU x c hxiso hc_tr *
    ⟨uEichler x h μ, uEichler_mem_su x h μ hxiso hxh hμ⟩, ?_, ?_⟩
  · rw [Submonoid.coe_mul, uTransvecSU_coe, hEcoe, ← Matrix.mulVec_mulVec, hE_x,
      uTransvection_apply_self x c hxiso]
  · rw [Submonoid.coe_mul, uTransvecSU_coe, hEcoe, ← Matrix.mulVec_mulVec, hE_y,
      uTransvection_mulVec, dotProduct_sub, hxy', dotProduct_smul, hxiso, smul_zero, sub_zero,
      mul_one]
    abel

/-- **Exact mate-transitivity fixing the ENTIRE perp `⟨x,y,y'⟩^⊥`.** Strengthens
`exists_su_fixes_maps_isotropic_mate`: the element `g = τ_{x,c}·E_{x,h,μ}` (`h = y'-y`) sending the
isotropic mate `y ↦ y'` of `x` (both `⟨x,·⟩ = 1`) also fixes *every* `z` with
`⟨x,z⟩ = ⟨y,z⟩ = ⟨y',z⟩ = 0` — the transvection `τ_{x,·}` fixes `x^⊥` and the Eichler `E_{x,h,·}`
fixes `⟨x,h⟩^⊥` (and `⟨h,z⟩ = ⟨y',z⟩ - ⟨y,z⟩ = 0` there). This is the mate-step engine of the
generation induction (unitary analogue of `offS_transvecFixing_maps_mate`): it carries `f₀ ↦ f₀'`
inside the line stabiliser of `e₀` while pinning the already-fixed pairs in the complement. -/
theorem exists_su_fixes_maps_isotropic_mate_fixing_perp (x y y' : Fin n → UnitaryField p)
    (hxiso : star x ⬝ᵥ x = 0) (hyiso : star y ⬝ᵥ y = 0) (hy'iso : star y' ⬝ᵥ y' = 0)
    (hxy : star x ⬝ᵥ y = 1) (hxy' : star x ⬝ᵥ y' = 1) :
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p),
      (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x = x ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ y = y' ∧
        ∀ z : Fin n → UnitaryField p, star x ⬝ᵥ z = 0 → star y ⬝ᵥ z = 0 → star y' ⬝ᵥ z = 0 →
          (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ z = z := by
  set h := y' - y with hh_def
  have hxh : star x ⬝ᵥ h = 0 := by rw [hh_def, dotProduct_sub, hxy, hxy', sub_self]
  obtain ⟨t, ht⟩ := exists_add_star_eq_neg_dotProduct_self p h
  set μ := -t with hμ_def
  have hμ : μ + star μ = star h ⬝ᵥ h := by rw [hμ_def, star_neg, ← neg_add, ht, neg_neg]
  set c := star h ⬝ᵥ y + μ with hc_def
  have hE_x : uEichler x h μ *ᵥ x = x := uEichler_apply_self x h μ hxiso hxh
  have hyh : y' = y + h := by rw [hh_def]; abel
  have hE_y : uEichler x h μ *ᵥ y = y' - c • x := by
    rw [uEichler_mulVec, hxy, one_smul, mul_one, hc_def, add_smul, hyh]
    abel
  have hc_tr : c + star c = 0 := by
    have hsc : star c = star y ⬝ᵥ h + star μ := by
      rw [hc_def, star_add]
      exact congrArg (· + star μ) (dotProduct_star_swap h y).symm
    have key : star h ⬝ᵥ y + star y ⬝ᵥ h + star h ⬝ᵥ h = 0 := by
      rw [hh_def]
      simp only [star_sub, sub_dotProduct, dotProduct_sub, hyiso, hy'iso]
      ring
    rw [hc_def, hsc]; linear_combination key + hμ
  have hEcoe : ((⟨uEichler x h μ, uEichler_mem_su x h μ hxiso hxh hμ⟩ :
      Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) :
      Matrix (Fin n) (Fin n) (UnitaryField p)) = uEichler x h μ := rfl
  refine ⟨uTransvecSU x c hxiso hc_tr *
    ⟨uEichler x h μ, uEichler_mem_su x h μ hxiso hxh hμ⟩, ?_, ?_, ?_⟩
  · rw [Submonoid.coe_mul, uTransvecSU_coe, hEcoe, ← Matrix.mulVec_mulVec, hE_x,
      uTransvection_apply_self x c hxiso]
  · rw [Submonoid.coe_mul, uTransvecSU_coe, hEcoe, ← Matrix.mulVec_mulVec, hE_y,
      uTransvection_mulVec, dotProduct_sub, hxy', dotProduct_smul, hxiso, smul_zero, sub_zero,
      mul_one]
    abel
  · intro z hxz hyz hy'z
    have hhz : star h ⬝ᵥ z = 0 := by rw [hh_def, star_sub, sub_dotProduct, hy'z, hyz, sub_zero]
    have hEz : uEichler x h μ *ᵥ z = z := by
      rw [uEichler_mulVec, hxz, hhz, mul_zero]; simp
    rw [Submonoid.coe_mul, uTransvecSU_coe, hEcoe, ← Matrix.mulVec_mulVec, hEz,
      uTransvection_mulVec, hxz, mul_zero, zero_smul, add_zero]

/-- **Weyl/swap element of a hyperbolic plane as a 3-transvection product.** For an isotropic
hyperbolic pair `(e,f)` (`⟨e,f⟩ = 1`, both isotropic) and a trace-zero `a ≠ 0`, the product
`τ_{e,a}·τ_{f,-a⁻¹}·τ_{e,a} ∈ SU` sends `e ↦ -a⁻¹·f` and `f ↦ a·e`, fixing `⟨e,f⟩^⊥` pointwise.
The off-diagonal scalar `-a⁻¹` is **automatically trace-zero** (`star a = -a ⟹ star(-a⁻¹) = a⁻¹`),
so all three factors are genuine isotropic unitary transvections. This realises the Weyl group of the
hyperbolic plane inside the transvection group — the seed of the diagonal torus
`D_λ = w(a')·w(a) : e ↦ -a⁻¹a'·e, f ↦ (-a⁻¹a')⁻¹·f` (`λ = -a⁻¹a' ∈ F_q*`), used to fix scalars in
the exact pair-transitivity of the generation induction. -/
theorem exists_su_weyl_swap (e f : Fin n → UnitaryField p)
    (hee : star e ⬝ᵥ e = 0) (hff : star f ⬝ᵥ f = 0) (hef : star e ⬝ᵥ f = 1)
    {a : UnitaryField p} (ha0 : a ≠ 0) (ha : a + star a = 0) :
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p),
      (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = (-a⁻¹) • f ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = a • e ∧
        ∀ z : Fin n → UnitaryField p, star e ⬝ᵥ z = 0 → star f ⬝ᵥ z = 0 →
          (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ z = z := by
  have hfe : star f ⬝ᵥ e = 1 := by rw [dotProduct_star_swap, hef, star_one]
  have hsa : star a = -a := by linear_combination ha
  have ha' : (-a⁻¹) + star (-a⁻¹) = 0 := by
    rw [star_neg, star_inv₀, hsa, inv_neg, neg_neg]; ring
  have hab : a * (-a⁻¹) = -1 := by rw [mul_neg, mul_inv_cancel₀ ha0]
  set b : UnitaryField p := -a⁻¹ with hb
  -- the three transvection actions, applied right-to-left
  have hcoe : ((uTransvecSU e a hee ha * uTransvecSU f b hff ha' * uTransvecSU e a hee ha :
      Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) :
      Matrix (Fin n) (Fin n) (UnitaryField p))
      = uTransvection e a * uTransvection f b * uTransvection e a := by
    simp only [Submonoid.coe_mul, uTransvecSU_coe]
  refine ⟨uTransvecSU e a hee ha * uTransvecSU f b hff ha' * uTransvecSU e a hee ha, ?_, ?_, ?_⟩
  · -- g·e = b•f
    have e1 : uTransvection e a *ᵥ e = e := by
      rw [uTransvection_mulVec, hee, mul_zero, zero_smul, add_zero]
    have e2 : uTransvection f b *ᵥ e = e + b • f := by
      rw [uTransvection_mulVec, hfe, mul_one]
    have e3 : uTransvection e a *ᵥ (e + b • f) = b • f := by
      rw [uTransvection_mulVec, dotProduct_add, hee, dotProduct_smul, hef, smul_eq_mul, mul_one,
        zero_add, hab, neg_one_smul]
      abel
    rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2, e3]
  · -- g·f = a•e
    have e1 : uTransvection e a *ᵥ f = f + a • e := by
      rw [uTransvection_mulVec, hef, mul_one]
    have e2 : uTransvection f b *ᵥ (f + a • e) = a • e := by
      rw [uTransvection_mulVec, dotProduct_add, hff, dotProduct_smul, hfe, smul_eq_mul, mul_one,
        zero_add, mul_comm b a, hab, neg_one_smul]
      abel
    have e3 : uTransvection e a *ᵥ (a • e) = a • e := by
      simp [uTransvection_mulVec, dotProduct_smul, hee]
    rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2, e3]
  · -- g fixes ⟨e,f⟩^⊥
    intro z hez hfz
    have e1 : uTransvection e a *ᵥ z = z := by
      rw [uTransvection_mulVec, hez, mul_zero, zero_smul, add_zero]
    have e2 : uTransvection f b *ᵥ z = z := by
      rw [uTransvection_mulVec, hfz, mul_zero, zero_smul, add_zero]
    rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2, e1]

/-- **Diagonal torus of a hyperbolic plane** (`λ ∈ F_q*`, i.e. `star λ = λ ≠ 0`). The product
`w(a')·w(a)` of two Weyl swaps (`a' = -a·λ`) is an `SU` element scaling `e ↦ λ·e`, `f ↦ λ⁻¹·f`
while fixing `⟨e,f⟩^⊥` pointwise. A 6-transvection product realising `diag(λ,λ⁻¹)` inside the
transvection group; `det = λ·λ⁻¹ = 1` and unitarity force `λ` into the fixed field `F_q`, matching
the `SU(2)` torus. This is the scalar-correction element of the exact pair-transitivity used in the
generation dimension induction (`hgen`): after the line-level move `e ↦ c·e'`, composing with the
appropriate `D_λ` rescales to land on `e'` exactly (when `c ∈ F_q*`). -/
theorem exists_su_hyperbolic_scale (e f : Fin n → UnitaryField p)
    (hee : star e ⬝ᵥ e = 0) (hff : star f ⬝ᵥ f = 0) (hef : star e ⬝ᵥ f = 1)
    {lam : UnitaryField p} (hlam0 : lam ≠ 0) (hlam : star lam = lam) :
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p),
      (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = lam • e ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = lam⁻¹ • f ∧
        ∀ z : Fin n → UnitaryField p, star e ⬝ᵥ z = 0 → star f ⬝ᵥ z = 0 →
          (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ z = z := by
  obtain ⟨a, ha0, hatr⟩ := UnitaryField.exists_traceZero_ne_zero p
  have hsa : star a = -a := by linear_combination hatr
  set a' : UnitaryField p := -a * lam with ha'def
  have ha'0 : a' ≠ 0 := by rw [ha'def]; exact mul_ne_zero (neg_ne_zero.mpr ha0) hlam0
  have ha'tr : a' + star a' = 0 := by
    rw [ha'def, star_mul', star_neg, hsa, hlam]; ring
  obtain ⟨g1, hg1e, hg1f, hg1z⟩ := exists_su_weyl_swap p e f hee hff hef ha0 hatr
  obtain ⟨g2, hg2e, hg2f, hg2z⟩ := exists_su_weyl_swap p e f hee hff hef ha'0 ha'tr
  -- the two scalar identities
  have hscaleE : (-a⁻¹) * a' = lam := by
    rw [ha'def]; field_simp
  have hscaleF : a * (-a'⁻¹) = lam⁻¹ := by
    rw [ha'def]; field_simp [ha0, hlam0]
  refine ⟨g2 * g1, ?_, ?_, ?_⟩
  · rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hg1e, Matrix.mulVec_smul, hg2f, smul_smul,
      hscaleE]
  · rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hg1f, Matrix.mulVec_smul, hg2e, smul_smul,
      hscaleF]
  · intro z hez hfz
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hg1z z hez hfz, hg2z z hez hfz]

/-- **Non-orthogonal move fixing the ENTIRE common perp `⟨v,w⟩^⊥`.** For isotropic `v, w` with
`⟨v,w⟩ ≠ 0`, the SAME element `g = τ_{v,b}·τ_{w,t} ∈ SU` mapping `v ↦ c·w` (`c ≠ 0`) fixes *every*
`x` orthogonal to both centres (`⟨v,x⟩ = ⟨w,x⟩ = 0`) — because each transvection `τ_{u,·}` fixes
`u^⊥`. This is the within-complement transitivity engine of the generation dimension induction
(unitary analogue of the symplectic `offS_transvecGen_maps`): applied with `e, f ∈ ⟨v,w⟩^⊥` it moves
`v` to the line of `w` while pinning a whole hyperbolic pair `(e,f)`. Strict generalisation of
`exists_su_fixes_maps_nonorth` (which fixes a single passed `x`). -/
theorem exists_su_maps_nonorth_fixing_perp (v w : Fin n → UnitaryField p)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0) (hvw : star v ⬝ᵥ w ≠ 0) :
    ∃ (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (c : UnitaryField p),
      c ≠ 0 ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ v = c • w ∧
        ∀ x : Fin n → UnitaryField p, star v ⬝ᵥ x = 0 → star w ⬝ᵥ x = 0 →
          (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x = x := by
  have hβ : star w ⬝ᵥ v = star (star v ⬝ᵥ w) := dotProduct_star_swap v w
  set β := star v ⬝ᵥ w with hβdef
  set Nβ := star β * β with hNdef
  have hNβ0 : Nβ ≠ 0 := mul_ne_zero (star_ne_zero.mpr hvw) hvw
  have hNβH : star Nβ = Nβ := by rw [hNdef, star_mul', star_star, mul_comm]
  obtain ⟨t, ht0, httr⟩ := UnitaryField.exists_traceZero_ne_zero p
  have hstart : star t = -t := by linear_combination httr
  set b := -(Nβ⁻¹ * t⁻¹) with hbdef
  have hb_tr : b + star b = 0 := by
    rw [hbdef, star_neg, star_mul', star_inv₀, star_inv₀, hNβH, hstart, inv_neg]
    ring
  have hcoef : b * (t * Nβ) = -1 := by
    rw [hbdef, neg_mul,
      show Nβ⁻¹ * t⁻¹ * (t * Nβ) = (Nβ⁻¹ * Nβ) * (t⁻¹ * t) by ring,
      inv_mul_cancel₀ hNβ0, inv_mul_cancel₀ ht0, mul_one]
  refine ⟨uTransvecSU v b hviso hb_tr * uTransvecSU w t hwiso httr, t * star β,
    mul_ne_zero ht0 (star_ne_zero.mpr hvw), ?_, ?_⟩
  · rw [Submonoid.coe_mul, uTransvecSU_coe, uTransvecSU_coe, ← Matrix.mulVec_mulVec,
      uTransvection_mulVec w t v, hβ, uTransvection_mulVec v b,
      dotProduct_add, dotProduct_smul, hviso, ← hβdef, smul_eq_mul, zero_add,
      show t * star β * β = t * Nβ by rw [hNdef]; ring, hcoef, neg_one_smul]
    abel
  · intro x hvx hwx
    rw [Submonoid.coe_mul, uTransvecSU_coe, uTransvecSU_coe, ← Matrix.mulVec_mulVec,
      uTransvection_mulVec w t x, hwx, mul_zero, zero_smul, add_zero,
      uTransvection_mulVec v b x, hvx, mul_zero, zero_smul, add_zero]

/-- **`SU` is transitive on isotropic lines** (`n ≥ 3`, machine-checked, no Witt classification):
for nonzero isotropic `v, w`, there is `g ∈ SU` with `g·v = c·w` (`c ≠ 0`), i.e. `g·[v] = [w]`.
Route through a common non-orthogonal isotropic `u` (`exists_common_nonorth_isotropic`, diameter-2
connectivity of the non-orthogonality graph): `g₁·v = c₁·u` and `g₂·u = c₂·w` by the non-orthogonal
move (`exists_su_maps_nonorth`), so `g₂g₁·v = (c₁c₂)·w`. This is the geometric core of unitary
pretransitivity on `IsoPoint`. -/
theorem exists_su_maps_isotropic (hn : 3 ≤ n) (v w : Fin n → UnitaryField p)
    (hv : v ≠ 0) (hw : w ≠ 0) (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0) :
    ∃ (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (c : UnitaryField p),
      c ≠ 0 ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ v = c • w := by
  obtain ⟨u, hu0, huiso, hvu, hwu⟩ :=
    exists_common_nonorth_isotropic p hn v w hv hw hviso hwiso
  obtain ⟨g1, c1, hc1, hg1⟩ := exists_su_maps_nonorth p v u hviso huiso hvu
  have huw : star u ⬝ᵥ w ≠ 0 := by
    rw [dotProduct_star_swap w u]; exact star_ne_zero.mpr hwu
  obtain ⟨g2, c2, hc2, hg2⟩ := exists_su_maps_nonorth p u w huiso hwiso huw
  refine ⟨g2 * g1, c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hg1, Matrix.mulVec_smul, hg2, smul_smul]

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

/-! ### `offSU` / `FixSU`: bookkeeping layer of the `hgen` generation induction

Coordinate analogues of the symplectic `offS` / `FixS` (`SpIwasawa.lean:460-614`). For the identity
Hermitian form `⟨x,y⟩ = star x ⬝ᵥ y` on `Fin n → F_{p²}` the standard basis is orthonormal
(`⟨e_j,x⟩ = x_j`), so "vanishing on a coordinate set `C`" coincides with "orthogonal to
`{e_j : j ∈ C}`". Consequently a `g ∈ SU` fixing those `e_j` (`FixSU C`) preserves the vanishing
condition (`offSU C`), and the perp-fixing Eichler engines (which fix the *whole* `⟨v,w⟩^⊥`) restrict
to `FixSU C` moves whenever the two centres lie in `offSU C`. This is the purely bookkeeping part of
the Dieudonné dimension induction; the genuinely deep step — exact transitivity on hyperbolic pairs
*fixing `C`* (the third-dimension determinant balance, `exists_scale`) — is isolated separately. -/

/-- Vectors vanishing on the coordinate set `C` (the unitary analogue of the symplectic `offS`). -/
def offSU (C : Finset (Fin n)) (x : Fin n → UnitaryField p) : Prop := ∀ j ∈ C, x j = 0

/-- `g ∈ SU` fixes the standard basis vectors indexed by `C` (the unitary analogue of `FixS`). -/
def FixSU (C : Finset (Fin n))
    (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) : Prop :=
  ∀ j ∈ C, (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ Pi.single j 1 = Pi.single j 1

theorem offSU_add {C : Finset (Fin n)} {x y : Fin n → UnitaryField p}
    (hx : offSU p C x) (hy : offSU p C y) : offSU p C (x + y) := fun j hj => by
  rw [Pi.add_apply, hx j hj, hy j hj, add_zero]

theorem offSU_sub {C : Finset (Fin n)} {x y : Fin n → UnitaryField p}
    (hx : offSU p C x) (hy : offSU p C y) : offSU p C (x - y) := fun j hj => by
  rw [Pi.sub_apply, hx j hj, hy j hj, sub_zero]

theorem offSU_smul {C : Finset (Fin n)} (a : UnitaryField p) {x : Fin n → UnitaryField p}
    (hx : offSU p C x) : offSU p C (a • x) := fun j hj => by
  rw [Pi.smul_apply, hx j hj, smul_zero]

/-- `Pi.single j a` vanishes on `C` when `j ∉ C`. -/
theorem offSU_single {C : Finset (Fin n)} {j : Fin n} (hj : j ∉ C) (a : UnitaryField p) :
    offSU p C (Pi.single j a) := fun i hi => by
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  simp [hne]

/-- The `j`-th coordinate as a Hermitian form value: `⟨e_j, y⟩ = star (e_j) ⬝ᵥ y = y_j`. -/
theorem coord_eq_form (j : Fin n) (y : Fin n → UnitaryField p) :
    star (Pi.single j (1 : UnitaryField p)) ⬝ᵥ y = y j := by
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul]

theorem FixSU_mul {C : Finset (Fin n)}
    {g h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)}
    (hg : FixSU p C g) (hh : FixSU p C h) : FixSU p C (g * h) := fun j hj => by
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hh j hj, hg j hj]

/-- **A `FixSU C` element preserves `offSU C`.** `(g·x)_j = ⟨e_j, g·x⟩ = ⟨g·e_j, g·x⟩ = ⟨e_j, x⟩
= x_j = 0` for `j ∈ C` (using `g·e_j = e_j` and the unitary form-preservation). -/
theorem offSU_preserved {C : Finset (Fin n)}
    {g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)} (hg : FixSU p C g)
    {x : Fin n → UnitaryField p} (hx : offSU p C x) :
    offSU p C ((g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x) := by
  intro j hj
  rw [← coord_eq_form p j ((g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x), ← hg j hj,
    u_preserves_form (Matrix.specialUnitaryGroup_le_unitaryGroup g.2), coord_eq_form p j x]
  exact hx j hj

/-- **A perp-fixing `SU` element with both centres in `offSU C` is a `FixSU C` move.** If `g` fixes
`⟨v,w⟩^⊥` pointwise and `v, w ∈ offSU C`, then each `e_j` (`j ∈ C`) is orthogonal to both `v` and
`w` (`⟨v,e_j⟩ = star (v_j) = 0`), hence fixed by `g`. This converts the Eichler perp-fixing engines
(`exists_su_maps_nonorth_fixing_perp`) into the `FixS`-style relative moves of the induction. -/
theorem FixSU_of_fixes_perp {C : Finset (Fin n)} {v w : Fin n → UnitaryField p}
    (hv : offSU p C v) (hw : offSU p C w)
    {g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)}
    (hfix : ∀ x : Fin n → UnitaryField p, star v ⬝ᵥ x = 0 → star w ⬝ᵥ x = 0 →
      (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x = x) :
    FixSU p C g := by
  intro j hj
  refine hfix _ ?_ ?_
  · rw [dotProduct_single, mul_one, Pi.star_apply, hv j hj, star_zero]
  · rw [dotProduct_single, mul_one, Pi.star_apply, hw j hj, star_zero]

/-- **Base case of the generation induction**: a `g ∈ SU` fixing every standard basis vector is the
identity (its columns are the `e_j`). Unitary analogue of `sp_eq_one_of_FixS_univ`. -/
theorem FixSU_univ_eq_one {g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)}
    (hg : FixSU p Finset.univ g) : g = 1 := by
  apply Subtype.ext
  show (g : Matrix (Fin n) (Fin n) (UnitaryField p)) = 1
  ext q r
  have hr : (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ Pi.single r 1 = Pi.single r 1 :=
    hg r (Finset.mem_univ r)
  have hentry : ((g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ Pi.single r 1) q
      = (g : Matrix (Fin n) (Fin n) (UnitaryField p)) q r := by
    rw [mulVec_single_one]; rfl
  rw [← hentry, hr]
  by_cases h : r = q
  · subst h; rw [Pi.single_eq_same, Matrix.one_apply_eq]
  · have hne : q ≠ r := fun hh => h hh.symm
    simp [hne]

/-- **The transvection subgroup `⟨transvections⟩` of `SU`** — the object of `hgen`
(`hgen ⟺ uTransvecGen = ⊤`). Closure of all unitary transvections (isotropic centre, trace-zero
scalar). -/
noncomputable def uTransvecGen :
    Subgroup (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) :=
  Subgroup.closure {h | ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p)
    (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0), h = uTransvecSU v a hv ha}

theorem uTransvecSU_mem_gen (v : Fin n → UnitaryField p) (a : UnitaryField p)
    (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0) :
    uTransvecSU v a hv ha ∈ uTransvecGen p (n := n) :=
  Subgroup.subset_closure ⟨v, a, hv, ha, rfl⟩

/-- **Within-`offSU C` non-orthogonal line move, in `⟨transvections⟩` and fixing `C`.** For isotropic
`v, w ∈ offSU C` non-orthogonal, the Eichler product `τ_{v,b}·τ_{w,t}` maps `v ↦ c·w` (`c ≠ 0`),
lies in `⟨transvections⟩` (a product of two generators), and fixes `C` (its centres `v, w` lie in
`offSU C`, so it fixes every `e_j`, `j ∈ C`, by `FixSU_of_fixes_perp`). The membership- and
`FixSU`-aware within-complement transitivity engine of the genAux induction (the on-`uTransvecGen`
analogue of `exists_su_maps_nonorth_fixing_perp`). -/
theorem offSU_maps_nonorth_gen {C : Finset (Fin n)} {v w : Fin n → UnitaryField p}
    (hv : offSU p C v) (hw : offSU p C w)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0) (hvw : star v ⬝ᵥ w ≠ 0) :
    ∃ (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (c : UnitaryField p),
      g ∈ uTransvecGen p (n := n) ∧ FixSU p C g ∧ c ≠ 0 ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ v = c • w := by
  have hβ : star w ⬝ᵥ v = star (star v ⬝ᵥ w) := dotProduct_star_swap v w
  set β := star v ⬝ᵥ w with hβdef
  set Nβ := star β * β with hNdef
  have hNβ0 : Nβ ≠ 0 := mul_ne_zero (star_ne_zero.mpr hvw) hvw
  have hNβH : star Nβ = Nβ := by rw [hNdef, star_mul', star_star, mul_comm]
  obtain ⟨t, ht0, httr⟩ := UnitaryField.exists_traceZero_ne_zero p
  have hstart : star t = -t := by linear_combination httr
  set b := -(Nβ⁻¹ * t⁻¹) with hbdef
  have hb_tr : b + star b = 0 := by
    rw [hbdef, star_neg, star_mul', star_inv₀, star_inv₀, hNβH, hstart, inv_neg]; ring
  have hcoef : b * (t * Nβ) = -1 := by
    rw [hbdef, neg_mul, show Nβ⁻¹ * t⁻¹ * (t * Nβ) = (Nβ⁻¹ * Nβ) * (t⁻¹ * t) by ring,
      inv_mul_cancel₀ hNβ0, inv_mul_cancel₀ ht0, mul_one]
  have hperp : ∀ x : Fin n → UnitaryField p, star v ⬝ᵥ x = 0 → star w ⬝ᵥ x = 0 →
      (↑(uTransvecSU v b hviso hb_tr * uTransvecSU w t hwiso httr) :
        Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x = x := by
    intro x hvx hwx
    rw [Submonoid.coe_mul, uTransvecSU_coe, uTransvecSU_coe, ← Matrix.mulVec_mulVec,
      uTransvection_mulVec w t x, hwx, mul_zero, zero_smul, add_zero,
      uTransvection_mulVec v b x, hvx, mul_zero, zero_smul, add_zero]
  refine ⟨uTransvecSU v b hviso hb_tr * uTransvecSU w t hwiso httr, t * star β,
    mul_mem (uTransvecSU_mem_gen p v b hviso hb_tr) (uTransvecSU_mem_gen p w t hwiso httr),
    FixSU_of_fixes_perp p hv hw hperp, mul_ne_zero ht0 (star_ne_zero.mpr hvw), ?_⟩
  rw [Submonoid.coe_mul, uTransvecSU_coe, uTransvecSU_coe, ← Matrix.mulVec_mulVec,
    uTransvection_mulVec w t v, hβ, uTransvection_mulVec v b,
    dotProduct_add, dotProduct_smul, hviso, ← hβdef, smul_eq_mul, zero_add,
    show t * star β * β = t * Nβ by rw [hNdef]; ring, hcoef, neg_one_smul]
  abel

/-- **Weyl swap in `⟨transvections⟩` and fixing `C`.** The 3-transvection product
`τ_{e,a}·τ_{f,-a⁻¹}·τ_{e,a}` (`e, f ∈ offSU C` a hyperbolic pair) sends `e ↦ -a⁻¹·f`, `f ↦ a·e`, lies
in `uTransvecGen`, and fixes `C` (centres `e, f ∈ offSU C`). Membership-aware `exists_su_weyl_swap`. -/
theorem exists_su_weyl_swap_gen {C : Finset (Fin n)} {e f : Fin n → UnitaryField p}
    (he : offSU p C e) (hf : offSU p C f)
    (hee : star e ⬝ᵥ e = 0) (hff : star f ⬝ᵥ f = 0) (hef : star e ⬝ᵥ f = 1)
    {a : UnitaryField p} (ha0 : a ≠ 0) (ha : a + star a = 0) :
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p), g ∈ uTransvecGen p (n := n) ∧
      FixSU p C g ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = (-a⁻¹) • f ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = a • e := by
  have hfe : star f ⬝ᵥ e = 1 := by rw [dotProduct_star_swap, hef, star_one]
  have hsa : star a = -a := by linear_combination ha
  have ha' : (-a⁻¹) + star (-a⁻¹) = 0 := by
    rw [star_neg, star_inv₀, hsa, inv_neg, neg_neg]; ring
  have hab : a * (-a⁻¹) = -1 := by rw [mul_neg, mul_inv_cancel₀ ha0]
  set b : UnitaryField p := -a⁻¹ with hb
  set g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) :=
    uTransvecSU e a hee ha * uTransvecSU f b hff ha' * uTransvecSU e a hee ha with hgdef
  have hcoe : (g : Matrix (Fin n) (Fin n) (UnitaryField p))
      = uTransvection e a * uTransvection f b * uTransvection e a := by
    rw [hgdef]; simp only [Submonoid.coe_mul, uTransvecSU_coe]
  have hge : (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = b • f := by
    have e1 : uTransvection e a *ᵥ e = e := by
      rw [uTransvection_mulVec, hee, mul_zero, zero_smul, add_zero]
    have e2 : uTransvection f b *ᵥ e = e + b • f := by rw [uTransvection_mulVec, hfe, mul_one]
    have e3 : uTransvection e a *ᵥ (e + b • f) = b • f := by
      rw [uTransvection_mulVec, dotProduct_add, hee, dotProduct_smul, hef, smul_eq_mul, mul_one,
        zero_add, hab, neg_one_smul]
      abel
    rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2, e3]
  have hgf : (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = a • e := by
    have e1 : uTransvection e a *ᵥ f = f + a • e := by rw [uTransvection_mulVec, hef, mul_one]
    have e2 : uTransvection f b *ᵥ (f + a • e) = a • e := by
      rw [uTransvection_mulVec, dotProduct_add, hff, dotProduct_smul, hfe, smul_eq_mul, mul_one,
        zero_add, mul_comm b a, hab, neg_one_smul]
      abel
    have e3 : uTransvection e a *ᵥ (a • e) = a • e := by
      simp [uTransvection_mulVec, dotProduct_smul, hee]
    rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2, e3]
  have hperp : ∀ z : Fin n → UnitaryField p, star e ⬝ᵥ z = 0 → star f ⬝ᵥ z = 0 →
      (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ z = z := by
    intro z hez hfz
    have e1 : uTransvection e a *ᵥ z = z := by
      rw [uTransvection_mulVec, hez, mul_zero, zero_smul, add_zero]
    have e2 : uTransvection f b *ᵥ z = z := by
      rw [uTransvection_mulVec, hfz, mul_zero, zero_smul, add_zero]
    rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2, e1]
  exact ⟨g, hgdef ▸ mul_mem (mul_mem (uTransvecSU_mem_gen p e a hee ha)
      (uTransvecSU_mem_gen p f b hff ha')) (uTransvecSU_mem_gen p e a hee ha),
    FixSU_of_fixes_perp p he hf hperp, hge, hgf⟩

/-- **Diagonal `F_q*`-torus of a hyperbolic plane, in `⟨transvections⟩` and fixing `C`.** For
`λ ∈ F_q*` (`star λ = λ ≠ 0`) and a hyperbolic pair `e, f ∈ offSU C`, the 6-transvection product
`w(a')·w(a)` scales `e ↦ λ·e`, `f ↦ λ⁻¹·f`, lies in `uTransvecGen`, and fixes `C`. This is the
within-plane scalar correction of the generation induction (the `F_q*` case of `UExactLineTrans`,
e.g. the last pair `|Cᶜ| = 2`, where the scalar is forced into the fixed field). -/
theorem exists_su_hyperbolic_scale_gen {C : Finset (Fin n)} {e f : Fin n → UnitaryField p}
    (he : offSU p C e) (hf : offSU p C f)
    (hee : star e ⬝ᵥ e = 0) (hff : star f ⬝ᵥ f = 0) (hef : star e ⬝ᵥ f = 1)
    {lam : UnitaryField p} (hlam0 : lam ≠ 0) (hlam : star lam = lam) :
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p), g ∈ uTransvecGen p (n := n) ∧
      FixSU p C g ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = lam • e ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = lam⁻¹ • f := by
  obtain ⟨a, ha0, hatr⟩ := UnitaryField.exists_traceZero_ne_zero p
  have hsa : star a = -a := by linear_combination hatr
  set a' : UnitaryField p := -a * lam with ha'def
  have ha'0 : a' ≠ 0 := by rw [ha'def]; exact mul_ne_zero (neg_ne_zero.mpr ha0) hlam0
  have ha'tr : a' + star a' = 0 := by rw [ha'def, star_mul', star_neg, hsa, hlam]; ring
  obtain ⟨g1, hg1mem, hg1fix, hg1e, hg1f⟩ := exists_su_weyl_swap_gen p he hf hee hff hef ha0 hatr
  obtain ⟨g2, hg2mem, hg2fix, hg2e, hg2f⟩ := exists_su_weyl_swap_gen p he hf hee hff hef ha'0 ha'tr
  have hscaleE : (-a⁻¹) * a' = lam := by rw [ha'def]; field_simp
  have hscaleF : a * (-a'⁻¹) = lam⁻¹ := by rw [ha'def]; field_simp [ha0, hlam0]
  refine ⟨g2 * g1, mul_mem hg2mem hg1mem, FixSU_mul p hg2fix hg1fix, ?_, ?_⟩
  · rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hg1e, Matrix.mulVec_smul, hg2f, smul_smul,
      hscaleE]
  · rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hg1f, Matrix.mulVec_smul, hg2e, smul_smul,
      hscaleF]

/-! ### Explicit coordinate hyperbolic pair (with span recovery) for the generation induction

The genAux dimension induction peels a pair of unfixed coordinates `{i,j}` at a time. The isotropic
hyperbolic pair on those coordinates is `hpA = e_i + c·e_j`, `hpB = 2⁻¹·(e_i − c·e_j)` (`N(c) = −1`),
which together span `span{e_i, e_j}` (`hpA + 2·hpB = 2·e_i`, `hpA − 2·hpB = 2c·e_j`). Hence a matrix
fixing both `hpA` and `hpB` fixes both `e_i` and `e_j` — the step that converts "fix the peeled
pair" into "fix the two coordinates" (`FixSU`). -/

/-- First vector of the coordinate hyperbolic pair on `{i,j}`: `e_i + c·e_j`. -/
noncomputable def hpA (i j : Fin n) (c : UnitaryField p) : Fin n → UnitaryField p :=
  Pi.single i 1 + Pi.single j c

/-- Second vector of the coordinate hyperbolic pair on `{i,j}`: `2⁻¹·(e_i − c·e_j)`. -/
noncomputable def hpB (i j : Fin n) (c : UnitaryField p) : Fin n → UnitaryField p :=
  (2⁻¹ : UnitaryField p) • (Pi.single i 1 + Pi.single j (-c))

theorem hpA_iso {i j : Fin n} (hij : i ≠ j) {c : UnitaryField p} (hc : c * star c = -1) :
    star (hpA p i j c) ⬝ᵥ hpA p i j c = 0 := isotropic_single_pair hij hc

theorem hpB_iso {i j : Fin n} (hij : i ≠ j) {c : UnitaryField p} (hc : c * star c = -1) :
    star (hpB p i j c) ⬝ᵥ hpB p i j c = 0 := by
  have hcn : (-c) * star (-c) = -1 := by rw [star_neg, neg_mul_neg]; exact hc
  rw [hpB, star_smul, smul_dotProduct, dotProduct_smul, isotropic_single_pair hij hcn,
    smul_zero, smul_zero]

theorem hpA_hpB_hyperbolic {i j : Fin n} (hij : i ≠ j) (h2 : (2 : UnitaryField p) ≠ 0)
    {c : UnitaryField p} (hc : c * star c = -1) :
    star (hpA p i j c) ⬝ᵥ hpB p i j c = 1 := by
  have hcross : star ((Pi.single i 1 : Fin n → UnitaryField p) + Pi.single j c) ⬝ᵥ
      ((Pi.single i 1 : Fin n → UnitaryField p) + Pi.single j (-c)) = 2 := by
    rw [star_add, ← Pi.single_star, ← Pi.single_star, star_one]
    simp only [add_dotProduct, dotProduct_add, single_dotProduct, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, mul_one, mul_zero, add_zero, zero_add,
      mul_neg]
    rw [mul_comm (star c) c, hc]; ring
  rw [hpA, hpB, dotProduct_smul, hcross, smul_eq_mul, inv_mul_cancel₀ h2]

theorem hpA_offSU {C : Finset (Fin n)} {i j : Fin n} (hi : i ∉ C) (hj : j ∉ C)
    (c : UnitaryField p) : offSU p C (hpA p i j c) :=
  offSU_add p (offSU_single p hi 1) (offSU_single p hj c)

theorem hpB_offSU {C : Finset (Fin n)} {i j : Fin n} (hi : i ∉ C) (hj : j ∉ C)
    (c : UnitaryField p) : offSU p C (hpB p i j c) :=
  offSU_smul p _ (offSU_add p (offSU_single p hi 1) (offSU_single p hj (-c)))

/-- Span recovery: `hpA + 2·hpB = 2·e_i`. -/
theorem hpA_add_two_hpB (i j : Fin n) (h2 : (2 : UnitaryField p) ≠ 0) (c : UnitaryField p) :
    hpA p i j c + (2 : UnitaryField p) • hpB p i j c
      = (2 : UnitaryField p) • (Pi.single i 1 : Fin n → UnitaryField p) := by
  rw [hpA, hpB, smul_smul, mul_inv_cancel₀ h2, one_smul, two_smul, Pi.single_neg]
  abel

/-- Span recovery: `hpA − 2·hpB = 2·(c·e_j)`. -/
theorem hpA_sub_two_hpB (i j : Fin n) (h2 : (2 : UnitaryField p) ≠ 0) (c : UnitaryField p) :
    hpA p i j c - (2 : UnitaryField p) • hpB p i j c
      = (2 : UnitaryField p) • (Pi.single j c : Fin n → UnitaryField p) := by
  rw [hpA, hpB, smul_smul, mul_inv_cancel₀ h2, one_smul, two_smul, Pi.single_neg]
  abel

/-- **Fixing the coordinate hyperbolic pair fixes the two coordinates.** Since `hpA, hpB` span
`span{e_i, e_j}` (`hpA ± 2·hpB`), a matrix `M` fixing both `hpA` and `hpB` fixes `e_i` and `e_j`.
The step of the genAux induction that converts "fix the peeled pair" into `FixSU` on the two
coordinates. -/
theorem fixes_coords_of_fixes_hpAB {i j : Fin n} (h2 : (2 : UnitaryField p) ≠ 0)
    {c : UnitaryField p} (hc0 : c ≠ 0)
    {M : Matrix (Fin n) (Fin n) (UnitaryField p)}
    (hA : M *ᵥ hpA p i j c = hpA p i j c) (hB : M *ᵥ hpB p i j c = hpB p i j c) :
    M *ᵥ (Pi.single i 1 : Fin n → UnitaryField p) = Pi.single i 1 ∧
      M *ᵥ (Pi.single j 1 : Fin n → UnitaryField p) = Pi.single j 1 := by
  have cancel : ∀ (a : UnitaryField p), a ≠ 0 → ∀ x y : Fin n → UnitaryField p,
      a • x = a • y → x = y := fun a ha x y h => by
    have h' := congrArg (fun z => a⁻¹ • z) h
    simpa [smul_smul, inv_mul_cancel₀ ha] using h'
  refine ⟨cancel 2 h2 _ _ ?_, ?_⟩
  · rw [← Matrix.mulVec_smul, ← hpA_add_two_hpB p i j h2 c, Matrix.mulVec_add,
      Matrix.mulVec_smul, hA, hB, hpA_add_two_hpB p i j h2 c]
  · have hjc : M *ᵥ (Pi.single j c : Fin n → UnitaryField p) = Pi.single j c :=
      cancel 2 h2 _ _ (by
        rw [← Matrix.mulVec_smul, ← hpA_sub_two_hpB p i j h2 c, Matrix.mulVec_sub,
          Matrix.mulVec_smul, hA, hB, hpA_sub_two_hpB p i j h2 c])
    have hce : (Pi.single j c : Fin n → UnitaryField p)
        = c • (Pi.single j 1 : Fin n → UnitaryField p) := by
      funext m
      by_cases hm : j = m
      · subst hm; simp [Pi.single_eq_same, smul_eq_mul]
      · simp [Pi.single_eq_of_ne (Ne.symm hm)]
    rw [hce, Matrix.mulVec_smul] at hjc
    exact cancel c hc0 _ _ hjc

/-! ### The generation dimension induction (`genAux`), modulo exact pair-transitivity

The unitary analogue of the symplectic `genAux_le` (`SpIwasawa.lean:681`). Strong induction peeling a
pair of unfixed coordinates `{i,j}` at a time: map the (preserved) hyperbolic pair
`(g·hpA, g·hpB)` back to `(hpA, hpB)` by a transvection product `t` fixing `C`, so `t·g` fixes the two
new coordinates (`fixes_coords_of_fixes_hpAB`); recurse on `C ∪ {i,j}`; `g = t⁻¹·(t·g)`. Base
`Cᶜ.card ≤ 1`: `g` fixes every standard basis vector but (at most) one, so `g = 1` (`det` base case
`u_eq_one_of_fixes_all_but_one`). The ONE deep input — exact transitivity on hyperbolic pairs within
`offSU C`, landing in `⟨transvections⟩` (the unitary `offS_transvecGen_maps_pair`, which needs the
third-dimension determinant balance `exists_scale`) — is abstracted as the hypothesis `hpair`. -/

/-- **Base case of the generation induction.** A `g ∈ SU` fixing all standard basis vectors but at
most one (`Cᶜ.card ≤ 1`) is the identity (`det` base case), hence in `⟨transvections⟩`. -/
theorem uGenAux_base (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
    {C : Finset (Fin n)} (hsmall : Cᶜ.card ≤ 1) (hg : FixSU p C g) :
    g ∈ uTransvecGen p (n := n) := by
  have hu : star (g : Matrix (Fin n) (Fin n) (UnitaryField p)) * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  have hdet : (g : Matrix (Fin n) (Fin n) (UnitaryField p)).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  rcases Cᶜ.eq_empty_or_nonempty with hCe | ⟨k, hk⟩
  · have hCuniv : C = Finset.univ := (Finset.compl_eq_empty_iff C).mp hCe
    subst hCuniv
    rw [FixSU_univ_eq_one p hg]; exact one_mem _
  · have hg1 : (g : Matrix (Fin n) (Fin n) (UnitaryField p)) = 1 := by
      apply u_eq_one_of_fixes_all_but_one hu hdet (k := k)
      intro i hik
      apply hg i
      by_contra hiC
      exact hik (Finset.card_le_one.mp hsmall i (Finset.mem_compl.mpr hiC) k hk)
    rw [show g = 1 from Subtype.ext hg1]; exact one_mem _

/-- **The unitary generation induction, modulo exact pair-transitivity `hpair`.** Any `g ∈ SU`
fixing the standard basis vectors indexed by `C` lies in `⟨transvections⟩`. -/
theorem uGenAux (h2 : (2 : UnitaryField p) ≠ 0)
    (hpair : ∀ (C : Finset (Fin n)) (e f e' f' : Fin n → UnitaryField p),
      offSU p C e → offSU p C f → offSU p C e' → offSU p C f' →
      star e ⬝ᵥ e = 0 → star f ⬝ᵥ f = 0 → star e ⬝ᵥ f = 1 →
      star e' ⬝ᵥ e' = 0 → star f' ⬝ᵥ f' = 0 → star e' ⬝ᵥ f' = 1 →
      ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p), g ∈ uTransvecGen p (n := n) ∧
        FixSU p C g ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = e' ∧
          (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = f') :
    ∀ (steps : ℕ) (C : Finset (Fin n))
      (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)),
      Cᶜ.card ≤ steps → FixSU p C g → g ∈ uTransvecGen p (n := n) := by
  obtain ⟨c, hcnorm⟩ := UnitaryField.exists_norm_neg_one p
  have hc0 : c ≠ 0 := fun h => by simp [h] at hcnorm
  intro steps
  induction steps with
  | zero =>
    intro C g hCn hg
    -- `Cᶜ.card ≤ 0`, so `g` fixes every basis vector ⟹ `g = 1`
    exact uGenAux_base p g (by omega) hg
  | succ steps ih =>
    intro C g hCn hg
    by_cases hsmall : Cᶜ.card ≤ 1
    · exact uGenAux_base p g hsmall hg
    · -- peel a pair of unfixed coordinates
      have h1lt : 1 < Cᶜ.card := not_le.mp hsmall
      obtain ⟨i, hiCc, j, hjCc, hij⟩ := Finset.one_lt_card.mp h1lt
      have hiC : i ∉ C := Finset.mem_compl.mp hiCc
      have hjC : j ∉ C := Finset.mem_compl.mp hjCc
      -- the preserved hyperbolic pair `(g·hpA, g·hpB)`
      have hgu : (g : Matrix (Fin n) (Fin n) (UnitaryField p)) ∈ Matrix.unitaryGroup (Fin n) _ :=
        Matrix.specialUnitaryGroup_le_unitaryGroup g.2
      have hAiso : star (hpA p i j c) ⬝ᵥ hpA p i j c = 0 := hpA_iso p hij hcnorm
      have hBiso : star (hpB p i j c) ⬝ᵥ hpB p i j c = 0 := hpB_iso p hij hcnorm
      have hABhyp : star (hpA p i j c) ⬝ᵥ hpB p i j c = 1 := hpA_hpB_hyperbolic p hij h2 hcnorm
      obtain ⟨t, htmem, htfix, htA, htB⟩ := hpair C
        ((g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ hpA p i j c)
        ((g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ hpB p i j c)
        (hpA p i j c) (hpB p i j c)
        (offSU_preserved p hg (hpA_offSU p hiC hjC c))
        (offSU_preserved p hg (hpB_offSU p hiC hjC c))
        (hpA_offSU p hiC hjC c) (hpB_offSU p hiC hjC c)
        (by rw [u_preserves_form hgu]; exact hAiso)
        (by rw [u_preserves_form hgu]; exact hBiso)
        (by rw [u_preserves_form hgu]; exact hABhyp)
        hAiso hBiso hABhyp
      -- `t·g` fixes `hpA` and `hpB`, hence `e_i` and `e_j`
      have htgA : (↑(t * g) : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ hpA p i j c
          = hpA p i j c := by rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, htA]
      have htgB : (↑(t * g) : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ hpB p i j c
          = hpB p i j c := by rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, htB]
      obtain ⟨hgi, hgj⟩ := fixes_coords_of_fixes_hpAB p h2 hc0 htgA htgB
      -- `t·g` fixes `C ∪ {i,j}`
      have htgfix : FixSU p (insert i (insert j C)) (t * g) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        rcases hk with rfl | hk
        · exact hgi
        · rw [Finset.mem_insert] at hk
          rcases hk with rfl | hk
          · exact hgj
          · exact (FixSU_mul p htfix hg) k hk
      -- the complement shrinks by two
      have hcard : (insert i (insert j C))ᶜ.card ≤ steps := by
        have hijnotin : i ∉ insert j C := by
          simp only [Finset.mem_insert, not_or]; exact ⟨hij, hiC⟩
        have e1 : (insert i (insert j C)).card = C.card + 2 := by
          rw [Finset.card_insert_of_notMem hijnotin, Finset.card_insert_of_notMem hjC]
        have e2 : (insert i (insert j C))ᶜ.card = n - (C.card + 2) := by
          rw [Finset.card_compl, Fintype.card_fin, e1]
        have e3 : Cᶜ.card = n - C.card := by rw [Finset.card_compl, Fintype.card_fin]
        have e4 : C.card ≤ n := by
          have := Finset.card_le_univ C; rwa [Fintype.card_fin] at this
        omega
      have htgmem : (t * g) ∈ uTransvecGen p (n := n) :=
        ih (insert i (insert j C)) (t * g) hcard htgfix
      have hgeq : g = t⁻¹ * (t * g) := by group
      rw [hgeq]; exact mul_mem (inv_mem htmem) htgmem

/-- **The single deep input to `hgen`**: exact transitivity on hyperbolic pairs within `offSU C`,
landing in `⟨transvections⟩` (the unitary `offS_transvecGen_maps_pair`). Discharging this — which
requires the third-dimension determinant balance `exists_scale` (`n ≥ 3` essential) — completes the
proof that unitary transvections generate `SU`. -/
def UExactPairTrans : Prop :=
  ∀ (C : Finset (Fin n)) (e f e' f' : Fin n → UnitaryField p),
    offSU p C e → offSU p C f → offSU p C e' → offSU p C f' →
    star e ⬝ᵥ e = 0 → star f ⬝ᵥ f = 0 → star e ⬝ᵥ f = 1 →
    star e' ⬝ᵥ e' = 0 → star f' ⬝ᵥ f' = 0 → star e' ⬝ᵥ f' = 1 →
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p), g ∈ uTransvecGen p (n := n) ∧
      FixSU p C g ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = e' ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = f'

/-- **Unitary transvections generate `SU`, modulo `UExactPairTrans`** — i.e. `hgen` reduced to the
single deep pair-transitivity step. Instantiates the generation induction `uGenAux` at `C = ∅`
(`FixSU ∅` is vacuous). -/
theorem uTransvecGen_eq_top_of_hpair (h2 : (2 : UnitaryField p) ≠ 0)
    (hpair : UExactPairTrans p (n := n)) : uTransvecGen p (n := n) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  exact uGenAux p h2 hpair (∅ : Finset (Fin n))ᶜ.card ∅ g le_rfl
    (fun j hj => absurd hj (Finset.notMem_empty j))

/-- **`hgen` reduced to `UExactPairTrans`**: the literal generation hypothesis of
`commutator_SU_eq_top_of_generate` follows from the single deep pair-transitivity step (the closure
of the transvection set is `uTransvecGen`). -/
theorem hgen_of_hpair (h2 : (2 : UnitaryField p) ≠ 0) (hpair : UExactPairTrans p (n := n)) :
    Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p)
        (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤ :=
  uTransvecGen_eq_top_of_hpair p h2 hpair

/-- **Exact transitivity on isotropic VECTORS within `offSU C`, in `⟨transvections⟩`** (the deep
single-vector step). The line move `offSU_maps_nonorth_gen` gives `e ↦ c·e'`; killing the scalar `c`
needs the third-dimension `F_{q²}*` line-stabiliser scaling `exists_scale` (`n ≥ 3`). This is the
genuine remaining wall. -/
def UExactLineTrans : Prop :=
  ∀ (C : Finset (Fin n)) (e e' : Fin n → UnitaryField p),
    offSU p C e → offSU p C e' → star e ⬝ᵥ e = 0 → star e' ⬝ᵥ e' = 0 → e ≠ 0 → e' ≠ 0 →
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p), g ∈ uTransvecGen p (n := n) ∧
      FixSU p C g ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = e'

/-- **Exact transitivity on hyperbolic MATES within `offSU C`, in `⟨transvections⟩`** (fixing `e`).
The scalar is automatically pinned to `1` (both `f, f'` satisfy `⟨e,·⟩ = 1`, preserved by the
`e`-fixing move), so — unlike the line step — this needs NO third-dimension torus, only the Eichler
mate engine `exists_su_fixes_maps_isotropic_mate_fixing_perp` upgraded to `⟨transvections⟩` membership
(via Eichler = product of transvections). The unitary `offS_transvecFixing_maps_mate` analogue. -/
def UExactMateTrans : Prop :=
  ∀ (C : Finset (Fin n)) (e f f' : Fin n → UnitaryField p),
    offSU p C e → offSU p C f → offSU p C f' →
    star e ⬝ᵥ e = 0 → star f ⬝ᵥ f = 0 → star f' ⬝ᵥ f' = 0 →
    star e ⬝ᵥ f = 1 → star e ⬝ᵥ f' = 1 →
    ∃ g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p), g ∈ uTransvecGen p (n := n) ∧
      FixSU p C g ∧ (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ e = e ∧
        (g : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f = f'

/-- **`UExactPairTrans ⟸ UExactLineTrans + UExactMateTrans`** — the unitary
`offS_transvecGen_maps_pair` assembly: map `e ↦ e'` exactly (line step `t₁`), then fix `e'` and map
the preserved mate `t₁·f ↦ f'` (mate step `t₂`); `g = t₂·t₁`. Purely group-theoretic given the two
sub-moves, so it isolates the deep content into `UExactLineTrans` alone (the mate step carries no
torus). -/
theorem UExactPairTrans_of_line_mate (hline : UExactLineTrans p (n := n))
    (hmate : UExactMateTrans p (n := n)) : UExactPairTrans p (n := n) := by
  intro C e f e' f' he hf he' hf' heiso hfiso hef he'iso hf'iso he'f'
  have he0 : e ≠ 0 := by
    rintro rfl; rw [star_zero, zero_dotProduct] at hef; exact one_ne_zero hef.symm
  have he'0 : e' ≠ 0 := by
    rintro rfl; rw [star_zero, zero_dotProduct] at he'f'; exact one_ne_zero he'f'.symm
  obtain ⟨t1, ht1mem, ht1fix, ht1e⟩ := hline C e e' he he' heiso he'iso he0 he'0
  -- `t₁·f` is an isotropic mate of `e'`
  have hgu : (t1 : Matrix (Fin n) (Fin n) (UnitaryField p)) ∈ Matrix.unitaryGroup (Fin n) _ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup t1.2
  have ht1f_off : offSU p C ((t1 : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f) :=
    offSU_preserved p ht1fix hf
  have ht1f_iso : star ((t1 : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f) ⬝ᵥ
      ((t1 : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f) = 0 := by
    rw [u_preserves_form hgu]; exact hfiso
  have hmatecond : star e' ⬝ᵥ ((t1 : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f) = 1 := by
    rw [← ht1e, u_preserves_form hgu]; exact hef
  obtain ⟨t2, ht2mem, ht2fix, ht2e', ht2f⟩ := hmate C e'
    ((t1 : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ f) f'
    he' ht1f_off hf' he'iso ht1f_iso hf'iso hmatecond he'f'
  refine ⟨t2 * t1, mul_mem ht2mem ht1mem, FixSU_mul p ht2fix ht1fix, ?_, ?_⟩
  · rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ht1e, ht2e']
  · rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ht2f]

/-- **`hgen` reduced to the line + mate steps**: `hgen ⟸ UExactLineTrans + UExactMateTrans + (2≠0)`.
The mate step is dischargeable (Eichler-membership, no torus); the line step is the remaining deep
wall (`exists_scale`). -/
theorem hgen_of_line_mate (h2 : (2 : UnitaryField p) ≠ 0)
    (hline : UExactLineTrans p (n := n)) (hmate : UExactMateTrans p (n := n)) :
    Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p)
        (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤ :=
  hgen_of_hpair p h2 (UExactPairTrans_of_line_mate p hline hmate)

/-- **`SU_n(F_{p²})` is perfect, modulo the unitary Witt generation theorem** (`n ≥ 3`, `p ≥ 5`).
Assembles `commutator_specialUnitaryGroup_eq_top` with the concrete fixed-field scalar
(`exists_fixedField_norm_ne_one`, `p ≥ 5`) and hyperbolic partners (`exists_hyperbolic_partner`).
The sole remaining input is `hgen` — that unitary transvections generate `SU` (Step 3a, submitted
to Aristotle). Once `hgen` is discharged this becomes unconditional and supplies the Iwasawa
`is_perfect` obligation for `PSUConcrete n p`. -/
theorem commutator_SU_eq_top_of_generate (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p)
        (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤) :
    commutator (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) = ⊤ := by
  obtain ⟨lam, hlam, hfix, hN⟩ := UnitaryField.exists_fixedField_norm_ne_one p hp
  exact commutator_specialUnitaryGroup_eq_top lam hlam hfix hN
    (exists_hyperbolic_partner p hn) hgen

end Concrete

/-! ### The `PSU = SU/Z` action on isotropic projective points, and faithfulness

`SU_n(F_{p²})` is **not** transitive on the full projective space `ℙ(Fⁿ)` (isotropic and
anisotropic points sit in separate orbits), so the Iwasawa action for `PSU` lives on the
**isotropic** projective points. Faithfulness of the descended `PSU = SU/Z` action there is exactly
the kernel = center result assembled above: `ker ⊆ center` is `su_fixes_isotropic_imp_central`,
`center ⊆ ker` is `su_central_fixes_isotropic_line`. This mirrors `SpN.pspFaithful`/`pspPermHom`. -/

section Faithful

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

open UnitaryField

/-- **Isotropy is scale-invariant**: `⟨a·v, a·v⟩ = (star a · a)·⟨v,v⟩`. -/
theorem star_smul_dotProduct_self (a : UnitaryField p) (v : Fin n → UnitaryField p) :
    star (a • v) ⬝ᵥ (a • v) = (star a * a) * (star v ⬝ᵥ v) := by
  have hs : star (a • v) = star a • star v := by
    funext i
    simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul']
  rw [hs, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

/-- **Isotropy is well-defined on projective points**: `[v]` is isotropic iff `v` is. -/
theorem isIso_mk_iff {v : Fin n → UnitaryField p} (hv : v ≠ 0) :
    star (Projectivization.mk (UnitaryField p) v hv).rep ⬝ᵥ
        (Projectivization.mk (UnitaryField p) v hv).rep = 0 ↔ star v ⬝ᵥ v = 0 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (UnitaryField p) _ v
    (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [zero_smul] at ha; exact (Projectivization.rep_nonzero _) ha.symm
  rw [← ha, star_smul_dotProduct_self, mul_eq_zero,
    or_iff_right (mul_ne_zero (star_ne_zero.mpr ha0) ha0)]

/-- **The isotropic projective points** — the carrier of the `PSU`-Iwasawa action. -/
abbrev IsoPoint : Type _ :=
  { x : Projectivization (UnitaryField p) (Fin n → UnitaryField p) // star x.rep ⬝ᵥ x.rep = 0 }

/-- `SU` preserves isotropy of a projective point (form preservation). -/
theorem su_smul_isoPoint_mem (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
    {x : Projectivization (UnitaryField p) (Fin n → UnitaryField p)} (hx : star x.rep ⬝ᵥ x.rep = 0) :
    star (g • x).rep ⬝ᵥ (g • x).rep = 0 := by
  have hrep : g • x = Projectivization.mk (UnitaryField p) (g • x.rep)
      ((smul_ne_zero_iff_ne g).mpr x.rep_nonzero) := by
    conv_lhs => rw [← Projectivization.mk_rep x]
    rw [Projectivization.smul_mk]
  rw [hrep, isIso_mk_iff, su_smul_vec_def]
  exact u_isotropic_of_mem (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) hx

noncomputable instance instSMulIsoPoint :
    SMul (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (IsoPoint p n) where
  smul g x := ⟨g • x.1, su_smul_isoPoint_mem p n g x.2⟩

theorem isoPoint_smul_coe (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
    (x : IsoPoint p n) : (g • x).1 = g • x.1 := rfl

noncomputable instance instMulActionIsoPoint :
    MulAction (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (IsoPoint p n) where
  one_smul x := Subtype.ext (one_smul _ x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

/-- **`center ⊆ ker`**: a central `g ∈ SU` fixes every isotropic projective point. -/
theorem su_center_le_isoKer :
    Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) ≤
      (MulAction.toPermHom (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
        (IsoPoint p n)).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  obtain ⟨a, ha0, ha⟩ := UnitaryField.exists_traceZero_ne_zero p
  apply Equiv.ext
  intro x
  show g • x = x
  apply Subtype.ext
  rw [isoPoint_smul_coe]
  obtain ⟨b, hb⟩ := su_central_fixes_isotropic_line g hg (Projectivization.rep_nonzero x.1)
    x.2 a ha0 ha
  conv_lhs => rw [← Projectivization.mk_rep x.1]
  conv_rhs => rw [← Projectivization.mk_rep x.1]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨b, ?_⟩
  rw [su_smul_vec_def]
  exact hb.symm

/-- **`ker ⊆ center`** (`n ≥ 3`): a `g ∈ SU` fixing every isotropic projective point is central.
This is where the geometric crux (`su_fixes_isotropic_imp_central`) enters. -/
theorem su_isoKer_le_center (hn : 3 ≤ n) :
    (MulAction.toPermHom (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
        (IsoPoint p n)).ker ≤
      Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  apply su_fixes_isotropic_imp_central p hn g
  intro z hziso
  rcases eq_or_ne z 0 with h0 | h0
  · exact ⟨1, by subst h0; simp⟩
  · have hzmem : star (Projectivization.mk (UnitaryField p) z h0).rep ⬝ᵥ
        (Projectivization.mk (UnitaryField p) z h0).rep = 0 := (isIso_mk_iff p n h0).mpr hziso
    have hfix : g • (⟨Projectivization.mk (UnitaryField p) z h0, hzmem⟩ : IsoPoint p n) =
        ⟨Projectivization.mk (UnitaryField p) z h0, hzmem⟩ :=
      (Equiv.ext_iff.mp hg) _
    have h2 : g • Projectivization.mk (UnitaryField p) z h0 =
        Projectivization.mk (UnitaryField p) z h0 := congrArg Subtype.val hfix
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h2
    obtain ⟨c, hc⟩ := h2
    refine ⟨c, ?_⟩
    rw [← su_smul_vec_def]
    exact hc.symm

/-- The descended permutation representation `PSU = SU/Z → Sym(IsoPoint)`. -/
noncomputable def psuPermHom :
    PSUConcrete n p →* Equiv.Perm (IsoPoint p n) :=
  QuotientGroup.lift (Subgroup.center _)
    (MulAction.toPermHom (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (IsoPoint p n))
    (su_center_le_isoKer p n)

theorem psuPermHom_mk (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) :
    psuPermHom p n (QuotientGroup.mk g) =
      MulAction.toPermHom (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))
        (IsoPoint p n) g := rfl

/-- **`psuPermHom` is injective** (`n ≥ 3`) — its kernel is trivial because
`ker (toPermHom) = center`. -/
theorem psuPermHom_injective (hn : 3 ≤ n) :
    Function.Injective (psuPermHom p n) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ g =>
    rw [psuPermHom_mk] at hx
    exact (QuotientGroup.eq_one_iff g).mpr
      (su_isoKer_le_center p n hn (MonoidHom.mem_ker.mpr hx))

/-- **`PSU = SU/Z` acts on the isotropic projective points** — the Iwasawa `MulAction` obligation. -/
@[reducible]
noncomputable def psuAction :
    MulAction (PSUConcrete n p) (IsoPoint p n) :=
  MulAction.compHom _ (psuPermHom p n)

/-- **`PSU = SU/Z` acts faithfully on the isotropic projective points** (`n ≥ 3`) — the Iwasawa
`FaithfulSMul` obligation, the assembly of the whole step-2 kernel = center development. -/
@[reducible]
noncomputable def psuFaithful (hn : 3 ≤ n) :
    letI := psuAction p n
    FaithfulSMul (PSUConcrete n p) (IsoPoint p n) :=
  letI := psuAction p n
  { eq_of_smul_eq_smul := fun {g₁ g₂} hsmul => by
      apply psuPermHom_injective p n hn
      apply Equiv.ext
      intro x
      show g₁ • x = g₂ • x
      exact hsmul x }

/-- **The isotropic-point action set is nonempty** (`n ≥ 2`) — an isotropic vector exists
(`exists_isotropic`), giving an isotropic projective point. This is the Iwasawa primitivity/
pretransitivity nonemptiness input for `PSUConcrete`. -/
theorem nonempty_isoPoint (hn : 2 ≤ n) : Nonempty (IsoPoint p n) := by
  obtain ⟨v, hv, hiso⟩ := UnitaryField.exists_isotropic p n hn
  exact ⟨⟨Projectivization.mk (UnitaryField p) v hv, (isIso_mk_iff p n hv).mpr hiso⟩⟩

end Faithful

/-! ### The Iwasawa structure on `PSU = SU/Z ↷ IsoPoint`

The unitary analogue of `SpN.pspIwasawaStructure`. The family `Tline x` is the root subgroup
`uRootSubgroup x.rep` of the isotropic line `x`, pushed to `PSU = SU/Z`. Its three Iwasawa
obligations:

* `is_comm`: each `Tline x` is abelian (the `IsMulCommutative` instance on `uRootSubgroup`,
  preserved by `Subgroup.map`);
* `is_conj`: conjugation-equivariance `Tline (g • x) = conj g • Tline x` (via `uRootSubgroup_conj`
  through the quotient, plus the line-invariance `uRootSubgroup_smul`/`_rep`);
* `is_generator`: `iSup Tline = ⊤`, which reduces to the unitary Witt generation hypothesis (the
  transvections generate `SU` — Step 3a, at Aristotle). Taken as a hypothesis here.
-/

section Iwasawa

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

open UnitaryField

open scoped Pointwise

/-- The `PSU`-action of `mk g` equals the `SU`-action of `g` on an isotropic point. -/
theorem psu_mk_smul (g : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) (x : IsoPoint p n) :
    letI := psuAction p n
    (QuotientGroup.mk g : PSUConcrete n p) • x = g • x := by
  letI := psuAction p n
  show psuPermHom p n (QuotientGroup.mk g) x = g • x
  rw [psuPermHom_mk]
  rfl

/-- **`PSU = SU/Z` is pretransitive on the isotropic points `IsoPoint`** (`n ≥ 3`,
machine-checked) — the Iwasawa pretransitivity obligation, descended from `SU`'s transitivity on
isotropic lines (`exists_su_maps_isotropic`). For isotropic points `x, y`, a two-transvection
product maps `x.rep → c·y.rep`, so its image in `PSU` maps `x → y`. Unitary analogue of
`SpN.psp_isPretransitive`. -/
theorem psu_isPretransitive (hn : 3 ≤ n) :
    letI := psuAction p n
    MulAction.IsPretransitive (PSUConcrete n p) (IsoPoint p n) := by
  letI := psuAction p n
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, c, hc, hg⟩ := exists_su_maps_isotropic p hn x.1.rep y.1.rep
    (Projectivization.rep_nonzero x.1) (Projectivization.rep_nonzero y.1) x.2 y.2
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [psu_mk_smul p n g x]
  apply Subtype.ext
  rw [isoPoint_smul_coe]
  conv_lhs => rw [← Projectivization.mk_rep x.1]
  conv_rhs => rw [← Projectivization.mk_rep y.1]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨c, by rw [su_smul_vec_def]; exact hg.symm⟩

/-- **`hT1` DISCHARGED — `Stab[x]` is transitive on isotropic points non-perpendicular to `[x]`**
(`n ≥ 3`, machine-checked via the Eichler/Siegel transformation, NO Witt theorem). For isotropic
points `x, y, y'` with `⟨x,y⟩ ≠ 0` and `⟨x,y'⟩ ≠ 0`, there is `g ∈ PSU` fixing `[x]` and mapping
`[y] → [y']`. Rescale `y, y'` to hyperbolic mates of `x` (`⟨x,·⟩ = 1`; isotropy is scale-invariant)
and apply `exists_su_fixes_maps_isotropic_mate`: the resulting `g ∈ SU` fixes `x.rep` and maps the
rescaled `y` to the rescaled `y'`, so its image in `PSU = SU/Z` fixes `[x]` and sends `[y] → [y']`.
This is the last geometric atom of `PSU` simplicity — only the Witt generation `hgen` remains. -/
theorem psu_hT1 :
    letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y' := by
  letI := psuAction p n
  intro x y y' hxy hxy'
  set xr := x.1.rep with hxr
  set yr := y.1.rep with hyr
  set y'r := y'.1.rep with hy'r
  set y0 := (star xr ⬝ᵥ yr)⁻¹ • yr with hy0
  set y'0 := (star xr ⬝ᵥ y'r)⁻¹ • y'r with hy'0
  have hxx : star xr ⬝ᵥ xr = 0 := x.2
  have hy0iso : star y0 ⬝ᵥ y0 = 0 := by rw [hy0, star_smul_dotProduct_self, y.2, mul_zero]
  have hy'0iso : star y'0 ⬝ᵥ y'0 = 0 := by rw [hy'0, star_smul_dotProduct_self, y'.2, mul_zero]
  have hxy0 : star xr ⬝ᵥ y0 = 1 := by
    rw [hy0, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hxy]
  have hxy'0 : star xr ⬝ᵥ y'0 = 1 := by
    rw [hy'0, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hxy']
  obtain ⟨g, hgx, hgy⟩ :=
    exists_su_fixes_maps_isotropic_mate p xr y0 y'0 hxx hy0iso hy'0iso hxy0 hxy'0
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · rw [psu_mk_smul p n g x]
    apply Subtype.ext
    rw [isoPoint_smul_coe]
    conv_lhs => rw [← Projectivization.mk_rep x.1]
    conv_rhs => rw [← Projectivization.mk_rep x.1]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [su_smul_vec_def, one_smul]; exact hgx.symm⟩
  · rw [psu_mk_smul p n g y]
    apply Subtype.ext
    rw [isoPoint_smul_coe]
    conv_lhs => rw [← Projectivization.mk_rep y.1]
    conv_rhs => rw [← Projectivization.mk_rep y'.1]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(star xr ⬝ᵥ yr) * (star xr ⬝ᵥ y'r)⁻¹, ?_⟩
    rw [su_smul_vec_def]
    have h1 := hgy
    rw [hy0, hy'0, Matrix.mulVec_smul] at h1
    rw [SemigroupAction.mul_smul, ← h1, smul_smul, mul_inv_cancel₀ hxy, one_smul]

/-! ### Block-combinatorics scaffold (the non-perpendicular connectivity half of primitivity)

The unitary analogue of `SpN.block_mem_of_nonperp` / `block_univ_of_nonperp_pair`, reducing the
non-perpendicular part of block-triviality to the **T1** transitivity input (`Stab[x]` transitive on
isotropic points non-orthogonal to `[x]` — the Eichler atom, at Aristotle). The diameter-2
connectivity of the non-orthogonality graph (`exists_common_nonorth_isotropic`, already proven) does
the rest. The "non-perp" relation `⟨x,y⟩ = star x.rep ⬝ᵥ y.rep ≠ 0` is line-invariant. -/

/-- Form-value line-invariance, right slot: `⟨x, [z]⟩` is a nonzero multiple of `⟨x, z⟩`. -/
theorem form_rep_mk_right_smul (x : IsoPoint p n) {z : Fin n → UnitaryField p}
    (hz : z ≠ 0) :
    ∃ a : UnitaryField p, a ≠ 0 ∧
      star x.1.rep ⬝ᵥ (Projectivization.mk (UnitaryField p) z hz).rep
        = a * (star x.1.rep ⬝ᵥ z) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (UnitaryField p) z hz
  exact ⟨a, a.ne_zero, by rw [← ha, Units.smul_def, dotProduct_smul, smul_eq_mul]⟩

/-- Form-value line-invariance, left slot: `⟨[z], t⟩` is a nonzero multiple of `⟨z, t⟩`. -/
theorem form_rep_mk_left_smul {z : Fin n → UnitaryField p} (hz : z ≠ 0) (t : IsoPoint p n) :
    ∃ a : UnitaryField p, a ≠ 0 ∧
      star (Projectivization.mk (UnitaryField p) z hz).rep ⬝ᵥ t.1.rep
        = a * (star z ⬝ᵥ t.1.rep) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (UnitaryField p) z hz
  refine ⟨star a, star_ne_zero.mpr a.ne_zero, ?_⟩
  rw [← ha, Units.smul_def]
  have hs : star ((a : UnitaryField p) • z) = (star (a : UnitaryField p)) • star z := by
    funext i; simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul']
  rw [hs, smul_dotProduct, smul_eq_mul]

/-- **Block expansion via a non-perpendicular partner** (modulo T1). If `q, p' ∈ B` are
non-perpendicular and `w` is non-perpendicular to `q`, then `w ∈ B`: T1 makes `Stab[q]` transitive
on points non-perp to `[q]`, and `B` is `Stab[q]`-invariant since `q ∈ B`. -/
theorem block_mem_of_nonperp
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    {B : Set (IsoPoint p n)}
    (hB : letI := psuAction p n; MulAction.IsBlock (PSUConcrete n p) B)
    {q p' w : IsoPoint p n} (hq : q ∈ B) (hp' : p' ∈ B)
    (hqp' : star q.1.rep ⬝ᵥ p'.1.rep ≠ 0) (hqw : star q.1.rep ⬝ᵥ w.1.rep ≠ 0) :
    w ∈ B := by
  letI := psuAction p n
  obtain ⟨g, hgq, hgp'⟩ := hT1 hqp' hqw
  have hgB : g • B = B := hB.smul_eq_of_mem hq (by rw [hgq]; exact hq)
  rw [← hgp', ← hgB]
  exact Set.smul_mem_smul_set hp'

/-- **A block with a non-perpendicular pair is everything** (modulo T1). Connectivity of the
non-orthogonality graph (diameter ≤ 2, `exists_common_nonorth_isotropic`) plus
`block_mem_of_nonperp`. Unitary analogue of `SpN.block_univ_of_nonperp_pair`. -/
theorem block_univ_of_nonperp_pair (hn : 3 ≤ n)
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    {B : Set (IsoPoint p n)}
    (hB : letI := psuAction p n; MulAction.IsBlock (PSUConcrete n p) B)
    {q r : IsoPoint p n} (hq : q ∈ B) (hr : r ∈ B)
    (hqr : star q.1.rep ⬝ᵥ r.1.rep ≠ 0) :
    B = Set.univ := by
  letI := psuAction p n
  rw [Set.eq_univ_iff_forall]
  intro t
  by_cases hqt : star q.1.rep ⬝ᵥ t.1.rep ≠ 0
  · exact block_mem_of_nonperp p n hT1 hB hq hr hqr hqt
  · obtain ⟨z, hz0, hziso, hqz, htz⟩ := exists_common_nonorth_isotropic p hn q.1.rep t.1.rep
      (Projectivization.rep_nonzero q.1) (Projectivization.rep_nonzero t.1) q.2 t.2
    set Z : IsoPoint p n :=
      ⟨Projectivization.mk (UnitaryField p) z hz0, (isIso_mk_iff p n hz0).mpr hziso⟩ with hZ
    -- `⟨q, Z⟩ ≠ 0`, so `Z ∈ B`
    obtain ⟨a, ha0, haeq⟩ := form_rep_mk_right_smul p n q hz0
    have hqZ : star q.1.rep ⬝ᵥ Z.1.rep ≠ 0 := by rw [hZ, haeq]; exact mul_ne_zero ha0 hqz
    have hZB : Z ∈ B := block_mem_of_nonperp p n hT1 hB hq hr hqr hqZ
    -- `⟨Z, q⟩ ≠ 0` (skew/star of `⟨q, Z⟩`) and `⟨Z, t⟩ ≠ 0`, so `t ∈ B`
    have hZq : star Z.1.rep ⬝ᵥ q.1.rep ≠ 0 := by
      rw [dotProduct_star_swap q.1.rep Z.1.rep]; exact star_ne_zero.mpr hqZ
    obtain ⟨b, hb0, hbeq⟩ := form_rep_mk_left_smul p n hz0 t
    have hzt' : star z ⬝ᵥ t.1.rep ≠ 0 := by
      rw [dotProduct_star_swap t.1.rep z]; exact star_ne_zero.mpr htz
    have hZt : star Z.1.rep ⬝ᵥ t.1.rep ≠ 0 := by
      rw [hZ, hbeq]; exact mul_ne_zero hb0 hzt'
    exact block_mem_of_nonperp p n hT1 hB hZB hq hZq hZt

/-! ### Block-triviality for `PSU(3,q)`: the perpendicular case is vacuous (Witt index ≤ 1)

For `n = 3` the only remaining gap in primitivity — distinct *perpendicular* isotropic block points —
cannot occur: two perpendicular isotropic lines in a nondegenerate dim-3 Hermitian space are equal
(a 2-dim totally isotropic subspace would exceed the Witt index `⌊3/2⌋ = 1`). So block-triviality for
`n = 3` follows from the non-perpendicular half alone (`block_univ_of_nonperp_pair`), needing only the
T1 transitivity input — no perpendicular-case Eichler transitivity. -/

/-- **Perpendicular isotropic vectors in dim 3 are parallel.** For `n = 3`, two nonzero isotropic
vectors `x, y` with `⟨x,y⟩ = 0` are linearly dependent. Proof: if independent, take a common
non-orthogonal isotropic `u` (diameter-2 connectivity, `exists_common_nonorth_isotropic`); then
`u ∉ span{x,y}` (else `⟨x,u⟩ = 0`), so `{u,y,x}` is a basis of `F³`; the covector
`w = star x - c·star y` (`c = ⟨x,u⟩/⟨y,u⟩`) is dot-orthogonal to the whole basis, hence zero, giving
`star x = c·star y`, i.e. `x ∥ y` — contradicting independence. -/
theorem perp_isotropic_parallel (hn3 : n = 3)
    {x y : Fin n → UnitaryField p} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxiso : star x ⬝ᵥ x = 0) (hyiso : star y ⬝ᵥ y = 0)
    (hperp : star x ⬝ᵥ y = 0) :
    ∃ c : UnitaryField p, c • y = x := by
  classical
  by_cases hLI : LinearIndependent (UnitaryField p) ![y, x]
  · exfalso
    have hn : 3 ≤ n := hn3.ge
    obtain ⟨u, hu0, huiso, hxu, hyu⟩ :=
      exists_common_nonorth_isotropic p hn x y hx hy hxiso hyiso
    have hperp' : star y ⬝ᵥ x = 0 := by
      rw [dotProduct_star_swap, hperp, star_zero]
    -- `u ∉ span {y, x}`
    have hu_notmem : u ∉ Submodule.span (UnitaryField p) (Set.range ![y, x]) := by
      rw [Matrix.range_cons_cons_empty]
      intro hmem
      rw [Submodule.mem_span_pair] at hmem
      obtain ⟨a, b, hab⟩ := hmem
      exact hxu (by
        rw [← hab, dotProduct_add, dotProduct_smul, dotProduct_smul, hperp, hxiso,
          smul_zero, smul_zero, add_zero])
    have hind : LinearIndependent (UnitaryField p) (Fin.cons u ![y, x]) :=
      hLI.fin_cons hu_notmem
    have hcard : Fintype.card (Fin 3)
        = Module.finrank (UnitaryField p) (Fin n → UnitaryField p) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_fin, hn3]
    have hspan : Submodule.span (UnitaryField p) (Set.range (Fin.cons u ![y, x])) = ⊤ :=
      hind.span_eq_top_of_card_eq_finrank hcard
    set c : UnitaryField p := (star x ⬝ᵥ u) * (star y ⬝ᵥ u)⁻¹ with hc
    set w : Fin n → UnitaryField p := star x - c • star y with hw
    -- the covector `w` annihilates `x, y, u`
    have hwx : w ⬝ᵥ x = 0 := by
      rw [hw, sub_dotProduct, smul_dotProduct, hxiso, hperp', smul_zero, sub_zero]
    have hwy : w ⬝ᵥ y = 0 := by
      rw [hw, sub_dotProduct, smul_dotProduct, hperp, hyiso, smul_zero, sub_zero]
    have hwu : w ⬝ᵥ u = 0 := by
      rw [hw, sub_dotProduct, smul_dotProduct, smul_eq_mul, hc,
        mul_assoc, inv_mul_cancel₀ hyu, mul_one, sub_self]
    -- `z ↦ w ⬝ᵥ z` as a linear map, zero on the basis hence zero
    let L : (Fin n → UnitaryField p) →ₗ[UnitaryField p] UnitaryField p :=
      { toFun := fun z => w ⬝ᵥ z
        map_add' := fun a b => dotProduct_add w a b
        map_smul' := fun s z => dotProduct_smul s w z }
    have hL0 : L = 0 := by
      refine LinearMap.ext_on_range hspan (fun i => ?_)
      fin_cases i
      · exact hwu
      · exact hwy
      · exact hwx
    have hwzero : w = 0 := by
      funext j
      rw [Pi.zero_apply]
      have : w ⬝ᵥ Pi.single j 1 = 0 := congrFun (congrArg DFunLike.coe hL0) (Pi.single j 1)
      rwa [dotProduct_single, mul_one] at this
    have hstarx : star x = c • star y := by
      rw [hw] at hwzero; exact sub_eq_zero.mp hwzero
    -- `star x = c•star y ⟹ x = star c • y`, contradicting independence of `![y, x]`
    have hxy : (star c) • y = x := by
      have h := congrArg star hstarx
      rw [star_star] at h
      have hss : star (c • star y) = star c • y := by
        funext i; simp [smul_eq_mul, star_mul']
      rw [hss] at h; exact h.symm
    exact (LinearIndependent.pair_iff' hy).mp hLI (star c) hxy
  · rw [LinearIndependent.pair_iff' hy, not_forall_not] at hLI
    obtain ⟨c, hc⟩ := hLI
    exact ⟨c, hc⟩

/-- **Distinct isotropic points in dim 3 are non-perpendicular.** The point-level contrapositive of
`perp_isotropic_parallel`: if `q ≠ r` as isotropic lines (`n = 3`) then `⟨q,r⟩ ≠ 0`. -/
theorem isoPoint_nonperp_of_ne (hn3 : n = 3) {q r : IsoPoint p n} (hqr : q ≠ r) :
    star q.1.rep ⬝ᵥ r.1.rep ≠ 0 := by
  intro hperp
  obtain ⟨c, hc⟩ := perp_isotropic_parallel p n hn3
    (Projectivization.rep_nonzero q.1) (Projectivization.rep_nonzero r.1) q.2 r.2 hperp
  apply hqr
  apply Subtype.ext
  rw [← Projectivization.mk_rep q.1, ← Projectivization.mk_rep r.1,
    Projectivization.mk_eq_mk_iff']
  exact ⟨c, hc⟩

/-- **Block-triviality for `PSU(3,q)`** (`n = 3`), modulo the T1 transitivity input. The
perpendicular case of primitivity is vacuous in dimension 3 (`isoPoint_nonperp_of_ne`), so every
block with ≥ 2 points contains a non-perpendicular pair, hence is everything
(`block_univ_of_nonperp_pair`). Unitary analogue of `SpN.psp_isTrivialBlock_of_isBlock`, but the
perp case collapses by the Witt-index-≤-1 vacuity rather than a second Eichler transitivity. -/
theorem psu3_isTrivialBlock_of_isBlock (hn3 : n = 3)
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    {B : Set (IsoPoint p n)}
    (hB : letI := psuAction p n; MulAction.IsBlock (PSUConcrete n p) B) :
    letI := psuAction p n; MulAction.IsTrivialBlock B := by
  letI := psuAction p n
  by_cases hs : B.Subsingleton
  · exact Or.inl hs
  · right
    rw [Set.not_subsingleton_iff] at hs
    obtain ⟨q, hq, r, hr, hqr⟩ := hs
    exact block_univ_of_nonperp_pair p n hn3.ge hT1 hB hq hr
      (isoPoint_nonperp_of_ne p n hn3 hqr)

/-- **Block-triviality for `PSU(n,q)`, general `n ≥ 3`**, modulo the three geometric Eichler atoms:
`hT1` (`Stab[x]` transitive on isotropic points non-perpendicular to `[x]`), `hT2` (`Stab[x]`
transitive on isotropic points *perpendicular* to `[x]`), and `hSep` (isotropic separation: distinct
perpendicular isotropic points admit an isotropic `s ⊥ x` non-perpendicular to `y`). The unitary
analogue of `SpN.psp_isTrivialBlock_of_isBlock`. For `n = 3` the perpendicular branch is unreachable
(`isoPoint_nonperp_of_ne`), so `psu3_isTrivialBlock_of_isBlock` needs only `hT1`; here the general
case routes the perpendicular subcase through `hSep` + `hT2` exactly as the symplectic proof. -/
theorem psu_isTrivialBlock_of_isBlock (hn : 3 ≤ n)
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    (hT2 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep = 0 → star x.1.rep ⬝ᵥ y'.1.rep = 0 →
        star y.1.rep ⬝ᵥ y'.1.rep ≠ 0 → ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    (hSep : ∀ {x y : IsoPoint p n}, x ≠ y → star x.1.rep ⬝ᵥ y.1.rep = 0 →
      ∃ s : Fin n → UnitaryField p, s ≠ 0 ∧ star s ⬝ᵥ s = 0 ∧
        star x.1.rep ⬝ᵥ s = 0 ∧ star y.1.rep ⬝ᵥ s ≠ 0)
    {B : Set (IsoPoint p n)}
    (hB : letI := psuAction p n; MulAction.IsBlock (PSUConcrete n p) B) :
    letI := psuAction p n; MulAction.IsTrivialBlock B := by
  letI := psuAction p n
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  · right
    rw [Set.not_subsingleton_iff] at hsub
    obtain ⟨x, hx, y, hy, hxy⟩ := hsub
    by_cases hperp : star x.1.rep ⬝ᵥ y.1.rep = 0
    · -- perpendicular case: introduce the separating isotropic point `S`
      obtain ⟨s, hs0, hsiso, hxs, hys⟩ := hSep hxy hperp
      set S : IsoPoint p n :=
        ⟨Projectivization.mk (UnitaryField p) s hs0, (isIso_mk_iff p n hs0).mpr hsiso⟩ with hS
      obtain ⟨a, ha0, haeq⟩ := form_rep_mk_right_smul p n x hs0
      have hxS : star x.1.rep ⬝ᵥ S.1.rep = 0 := by
        show star x.1.rep ⬝ᵥ (Projectivization.mk (UnitaryField p) s hs0).rep = 0
        rw [haeq, hxs, mul_zero]
      obtain ⟨a', ha'0, ha'eq⟩ := form_rep_mk_right_smul p n y hs0
      have hyS : star y.1.rep ⬝ᵥ S.1.rep ≠ 0 := by
        show star y.1.rep ⬝ᵥ (Projectivization.mk (UnitaryField p) s hs0).rep ≠ 0
        rw [ha'eq]; exact mul_ne_zero ha'0 hys
      -- T2 maps `y → S` inside `Stab[x]` (the pair `(y, S)` is non-perpendicular), so `S ∈ B`
      obtain ⟨g, hgx, hgy⟩ := hT2 hperp hxS hyS
      have hgB : g • B = B := hB.smul_eq_of_mem hx (by rw [hgx]; exact hx)
      have hSB : S ∈ B := by rw [← hgy, ← hgB]; exact Set.smul_mem_smul_set hy
      exact block_univ_of_nonperp_pair p n hn hT1 hB hy hSB hyS
    · -- non-perpendicular case: `(x,y)` is already a non-perp pair
      exact block_univ_of_nonperp_pair p n hn hT1 hB hx hy hperp

/-- **The `PSU`-level root subgroup along the isotropic line `x`** — the image in `SU/Z` of
`uRootSubgroup x.rep`. The Iwasawa family `T`. By `uRootSubgroup_rep`/`_smul` it depends only on
the line `x`. -/
noncomputable def Tline (x : IsoPoint p n) : Subgroup (PSUConcrete n p) :=
  (uRootSubgroup x.1.rep x.2).map
    (QuotientGroup.mk' (Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))))

instance (x : IsoPoint p n) : IsMulCommutative (Tline p n x) := by
  unfold Tline; infer_instance

/-- `Tline` of an explicit isotropic-point `[v]` equals the image of `uRootSubgroup v`
(line-invariance). -/
theorem Tline_mk (v : Fin n → UnitaryField p) (hv0 : v ≠ 0)
    (hv : star v ⬝ᵥ v = 0)
    (hpt : star (Projectivization.mk (UnitaryField p) v hv0).rep ⬝ᵥ
      (Projectivization.mk (UnitaryField p) v hv0).rep = 0) :
    Tline p n ⟨Projectivization.mk (UnitaryField p) v hv0, hpt⟩
      = (uRootSubgroup v hv).map
          (QuotientGroup.mk' (Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)))) :=
  congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center _))) (uRootSubgroup_rep hv0 hv hpt)

/-- **The family `Tline` generates `PSU`** — the Iwasawa `is_generator` obligation, modulo the
unitary Witt generation hypothesis `hgen` (transvections generate `SU`). Each `τ_{v,a}` lies in
`Tline [v]` (for `v ≠ 0`) or is `1` (for `v = 0`), so the generators descend to `iSup Tline = ⊤`
in `SU/Z`. Unitary analogue of `SpN.Tline_iSup`. -/
theorem Tline_iSup
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤) :
    iSup (Tline p n) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p))) y
  have hsub : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} ≤
      (iSup (Tline p n)).comap (QuotientGroup.mk'
        (Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)))) := by
    rw [Subgroup.closure_le]
    rintro h ⟨v, a, hv, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    by_cases hv0 : v = 0
    · subst hv0
      have h0 : uTransvecSU (0 : Fin n → UnitaryField p) a hv ha = 1 := by
        apply Subtype.ext; simp [uTransvecSU_coe, uTransvection]
      rw [h0, map_one]; exact one_mem _
    · have hpt : star (Projectivization.mk (UnitaryField p) v hv0).rep ⬝ᵥ
          (Projectivization.mk (UnitaryField p) v hv0).rep = 0 := (isIso_mk_iff p n hv0).mpr hv
      have hmem : QuotientGroup.mk'
            (Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)))
            (uTransvecSU v a hv ha) ∈
          Tline p n ⟨Projectivization.mk (UnitaryField p) v hv0, hpt⟩ := by
        rw [Tline_mk p n v hv0 hv hpt]
        exact Subgroup.mem_map_of_mem _ (mem_uRootSubgroup hv |>.mpr ⟨a, ha, rfl⟩)
      exact le_iSup (Tline p n) _ hmem
  have hg : g ∈ (iSup (Tline p n)).comap (QuotientGroup.mk'
      (Subgroup.center (Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)))) := by
    have h := hsub
    rw [hgen] at h
    exact h (Subgroup.mem_top g)
  exact Subgroup.mem_comap.mp hg

/-- **The Iwasawa structure on `PSU = SU/Z ↷ IsoPoint`** — the family `Tline` of abelian root
subgroups (`is_comm`), conjugation-equivariant (`is_conj`, via `uRootSubgroup_conj` through the
quotient) and generating (`is_generator`, `Tline_iSup`, modulo the Witt generation hypothesis
`hgen`). Unitary analogue of `SpN.pspIwasawaStructure`. -/
noncomputable def psuIwasawaStructure
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤) :
    letI := psuAction p n
    MulAction.IwasawaStructure (PSUConcrete n p) (IsoPoint p n) :=
  letI := psuAction p n
  { T := Tline p n
    is_comm := fun x => inferInstance
    is_conj := fun g x => by
      obtain ⟨g_SU, hg⟩ := QuotientGroup.mk_surjective g
      have hne : (g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep ≠ 0 := by
        rw [← su_smul_vec_def]
        exact (smul_ne_zero_iff_ne g_SU).mpr (Projectivization.rep_nonzero x.1)
      have hgx1 : (g • x).1 = Projectivization.mk (UnitaryField p)
          ((g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep) hne := by
        rw [← hg, psu_mk_smul p n g_SU x, isoPoint_smul_coe]
        conv_lhs => rw [← Projectivization.mk_rep x.1]
        rw [Projectivization.smul_mk]
        rfl
      have hiso2 : star ((g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep) ⬝ᵥ
          ((g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep) = 0 :=
        u_isotropic_of_mem (Matrix.specialUnitaryGroup_le_unitaryGroup g_SU.2) x.2
      have hpar : uRootSubgroup ((g • x).1.rep) (g • x).2
          = uRootSubgroup ((g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep) hiso2 := by
        have hmk : Projectivization.mk (UnitaryField p) ((g • x).1.rep)
              (Projectivization.rep_nonzero _)
            = Projectivization.mk (UnitaryField p)
              ((g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep) hne := by
          rw [Projectivization.mk_rep]; exact hgx1
        rw [Projectivization.mk_eq_mk_iff'] at hmk
        obtain ⟨c, hc⟩ := hmk
        have hcne : c ≠ 0 := by
          rintro rfl; rw [zero_smul] at hc
          exact (Projectivization.rep_nonzero (g • x).1) hc.symm
        have hcviso : star (c • ((g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep)) ⬝ᵥ
            (c • ((g_SU : Matrix (Fin n) (Fin n) (UnitaryField p)) *ᵥ x.1.rep)) = 0 := by
          rw [hc]; exact (g • x).2
        rw [← uRootSubgroup_smul hcne hiso2 hcviso]
        exact uRootSubgroup_congr hc.symm (g • x).2 hcviso
      rw [show (MulAut.conj g) • Tline p n x = (Tline p n x).map (MulAut.conj g) from
            Subgroup.toSubmonoid_inj.mp rfl]
      show Tline p n (g • x) = (Tline p n x).map (MulAut.conj g)
      unfold Tline
      rw [hpar, ← uRootSubgroup_conj g_SU x.2]
      simp only [Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun z => ?_
      change (QuotientGroup.mk' (Subgroup.center _))
          ((g_SU : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)) * z * g_SU⁻¹)
        = MulAut.conj g ((QuotientGroup.mk' (Subgroup.center _)) z)
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ← hg]
      rfl
    is_generator := Tline_iSup p n hgen }

/-- **`PSU = SU/Z` is perfect** (`n ≥ 3`, `p ≥ 5`), modulo the unitary Witt generation hypothesis
`hgen`. Descends `commutator_SU_eq_top_of_generate` along the surjection `SU ↠ SU/Z`, exactly as
`SpN.commutator_PSp_eq_top`. -/
theorem commutator_PSU_eq_top_of_generate (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤) :
    commutator (PSUConcrete n p) = ⊤ := by
  set G := Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) with hG
  let f := QuotientGroup.mk' (Subgroup.center G)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hmap : commutator (PSUConcrete n p) = Subgroup.map f (commutator G) := by
    show ⁅(⊤ : Subgroup (PSUConcrete n p)), ⊤⁆ = Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [hmap, commutator_SU_eq_top_of_generate p hn hp hgen, Subgroup.map_top_of_surjective f hf]

/-- **`PSU_n(F_{p²}) = SU/Z` is simple** (`n ≥ 3`, `p ≥ 5`) — the Iwasawa criterion
(`IwasawaStructure.isSimpleGroup`) assembled from all five machine-checked obligations
(`Nontrivial` = `PSU_nontrivial`; `FaithfulSMul` = `psuFaithful`; perfectness =
`commutator_PSU_eq_top_of_generate`; the `IwasawaStructure` `psuIwasawaStructure`), **modulo two
outstanding inputs taken as hypotheses**: the unitary Witt generation `hgen` (transvections
generate `SU` — Step 3a, at Aristotle) and quasi-preprimitivity `hqpp` of the isotropic-point
action (the deep geometric core — Step 2c). The unitary analogue of
`SpN.PSpn_isSimpleGroup_of_perfect`; this is the axiom-clean reduction of `PSU_isSimpleGroup`. -/
theorem PSU_isSimpleGroup_of_generate_of_qpp (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤)
    (hqpp : letI := psuAction p n;
      MulAction.IsQuasiPreprimitive (PSUConcrete n p) (IsoPoint p n)) :
    IsSimpleGroup (PSUConcrete n p) := by
  letI := psuAction p n
  haveI : Nontrivial (PSUConcrete n p) := PSU_nontrivial p hn
  haveI : FaithfulSMul (PSUConcrete n p) (IsoPoint p n) := psuFaithful p n hn
  haveI : MulAction.IsQuasiPreprimitive (PSUConcrete n p) (IsoPoint p n) := hqpp
  exact (psuIwasawaStructure p n hgen).isSimpleGroup
    (commutator_PSU_eq_top_of_generate p n hn hp hgen) (psuFaithful p n hn)

/-- **`PSU_n(F_{p²})` is simple** (`n ≥ 3`, `p ≥ 5`), modulo the Witt generation `hgen` and
block-triviality `hblk`. **Pretransitivity is now machine-checked** (`psu_isPretransitive`), so
together with `hblk` it yields `IsPreprimitive`, hence quasi-preprimitivity via the mathlib bridge
`IsPreprimitive.isQuasiPreprimitive`. Only TWO inputs remain — the Witt generation (Step 3a, at
Aristotle) and primitivity/block-triviality (the maximal-parabolic core); everything else is
machine-checked. Axiom-clean. -/
theorem PSU_isSimpleGroup_of_generate (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤)
    (hblk : letI := psuAction p n; ∀ {B : Set (IsoPoint p n)},
      MulAction.IsBlock (PSUConcrete n p) B → MulAction.IsTrivialBlock B) :
    IsSimpleGroup (PSUConcrete n p) := by
  letI := psuAction p n
  haveI : MulAction.IsPretransitive (PSUConcrete n p) (IsoPoint p n) := psu_isPretransitive p n hn
  haveI : MulAction.IsPreprimitive (PSUConcrete n p) (IsoPoint p n) :=
    { isTrivialBlock_of_isBlock := hblk }
  exact PSU_isSimpleGroup_of_generate_of_qpp p n hn hp hgen inferInstance

/-- **`PSU(3, p²)` is simple** (`p ≥ 5`), modulo the Witt generation `hgen` and the T1 Eichler
transitivity input only. Combines `psu3_isTrivialBlock_of_isBlock` — where the perpendicular case of
primitivity is **vacuous** in dimension 3 (Witt index ≤ 1, `perp_isotropic_parallel`) — with the
headline reduction `PSU_isSimpleGroup_of_generate`. The block-triviality core is thereby discharged
for `n = 3` from T1 alone: no perpendicular-case Eichler transitivity is needed. The two remaining
inputs are the unitary Witt generation (Step 3a, at Aristotle) and T1 (Step 2c-b, at Aristotle). -/
theorem psu3_isSimpleGroup_of_generate_of_T1 (hn3 : n = 3) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤)
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y') :
    IsSimpleGroup (PSUConcrete n p) :=
  PSU_isSimpleGroup_of_generate p n hn3.ge hp hgen
    (fun {_B} hB => psu3_isTrivialBlock_of_isBlock p n hn3 hT1 hB)

/-- **`PSU_n(F_{p²})` is simple** (`n ≥ 3`, `p ≥ 5`) for general `n`, modulo the Witt generation
`hgen` and the three geometric Eichler atoms `hT1`, `hT2`, `hSep` (see `psu_isTrivialBlock_of_isBlock`).
This is the fully-general assembly: block-triviality for all `n` is routed through the perpendicular
separation + perp-transitivity exactly as in the symplectic case. For `n = 3` use
`psu3_isSimpleGroup_of_generate_of_T1` instead — there `hT2`/`hSep` are unnecessary (vacuous perp
case). The remaining inputs are all recognized Eichler/Witt-theory targets. -/
theorem PSU_isSimpleGroup_of_generate_of_eichler (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤)
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    (hT2 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep = 0 → star x.1.rep ⬝ᵥ y'.1.rep = 0 →
        star y.1.rep ⬝ᵥ y'.1.rep ≠ 0 → ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    (hSep : ∀ {x y : IsoPoint p n}, x ≠ y → star x.1.rep ⬝ᵥ y.1.rep = 0 →
      ∃ s : Fin n → UnitaryField p, s ≠ 0 ∧ star s ⬝ᵥ s = 0 ∧
        star x.1.rep ⬝ᵥ s = 0 ∧ star y.1.rep ⬝ᵥ s ≠ 0) :
    IsSimpleGroup (PSUConcrete n p) :=
  PSU_isSimpleGroup_of_generate p n hn hp hgen
    (fun {_B} hB => psu_isTrivialBlock_of_isBlock p n hn hT1 hT2 hSep hB)

/-- **The isotropic-separation hypothesis `hSep` reduces to the perpendicular-partner atom.** Given
that distinct perpendicular isotropic points `x ≠ y` admit an isotropic `v` with `⟨x,v⟩ = 1` and
`⟨y,v⟩ = 0` (`hPP` — a hyperbolic partner of `x` inside `y^⊥`, the unitary Witt-extension atom), the
full separation `hSep` follows by the machine-checked `exists_isotropic_perp_nonperp_of_perp_partner`.
This isolates the entire remaining separation content into the single clean existence `hPP`. -/
theorem hSep_of_perp_partner (hn : 3 ≤ n)
    (hPP : letI := psuAction p n; ∀ {x y : IsoPoint p n}, x ≠ y →
      star x.1.rep ⬝ᵥ y.1.rep = 0 → ∃ v : Fin n → UnitaryField p, star v ⬝ᵥ v = 0 ∧
        star x.1.rep ⬝ᵥ v = 1 ∧ star y.1.rep ⬝ᵥ v = 0) :
    ∀ {x y : IsoPoint p n}, x ≠ y → star x.1.rep ⬝ᵥ y.1.rep = 0 →
      ∃ s : Fin n → UnitaryField p, s ≠ 0 ∧ star s ⬝ᵥ s = 0 ∧
        star x.1.rep ⬝ᵥ s = 0 ∧ star y.1.rep ⬝ᵥ s ≠ 0 := by
  letI := psuAction p n
  intro x y hxy hperp
  obtain ⟨v, hviso, hxv, hyv⟩ := hPP hxy hperp
  exact exists_isotropic_perp_nonperp_of_perp_partner p hn y.2
    (Projectivization.rep_nonzero y.1) hperp hviso hxv hyv

/-- **`PSU_n(F_{p²})` is simple** (`n ≥ 3`, `p ≥ 5`), general `n`, reduced to the **minimal** set of
geometric atoms: the Witt generation `hgen`, the non-perp transitivity `hT1`, the perp transitivity
`hT2`, and the perpendicular-partner existence `hPP` (from which the full separation is recovered by
`hSep_of_perp_partner`). Every remaining hypothesis is now a single clean Eichler/Witt-extension
statement — no compound separation algebra remains. For `n = 3` use
`psu3_isSimpleGroup_of_generate_of_T1` (only `hgen` + `hT1`; perp atoms vacuous). -/
theorem PSU_isSimpleGroup_of_generate_of_eichler' (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤)
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    (hT2 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep = 0 → star x.1.rep ⬝ᵥ y'.1.rep = 0 →
        star y.1.rep ⬝ᵥ y'.1.rep ≠ 0 → ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y')
    (hPP : letI := psuAction p n; ∀ {x y : IsoPoint p n}, x ≠ y →
      star x.1.rep ⬝ᵥ y.1.rep = 0 → ∃ v : Fin n → UnitaryField p, star v ⬝ᵥ v = 0 ∧
        star x.1.rep ⬝ᵥ v = 1 ∧ star y.1.rep ⬝ᵥ v = 0) :
    IsSimpleGroup (PSUConcrete n p) :=
  PSU_isSimpleGroup_of_generate_of_eichler p n hn hp hgen hT1 hT2
    (fun hxy hperp => hSep_of_perp_partner p n hn hPP hxy hperp)

/-- **The perpendicular-partner atom `hPP` is DISCHARGED** (point level): distinct perpendicular
isotropic points `x ≠ y` always admit an isotropic `v` with `⟨x,v⟩ = 1`, `⟨y,v⟩ = 0`, by the
machine-checked `exists_isotropic_perp_partner`. The reps are nonzero isotropic and non-parallel
(distinct projective points), which is all the vector lemma needs. So `hPP` is **not** a remaining
hypothesis — it is a theorem. -/
theorem psu_hPP {x y : IsoPoint p n} (hxy : x ≠ y) (hperp : star x.1.rep ⬝ᵥ y.1.rep = 0) :
    ∃ v : Fin n → UnitaryField p, star v ⬝ᵥ v = 0 ∧
      star x.1.rep ⬝ᵥ v = 1 ∧ star y.1.rep ⬝ᵥ v = 0 := by
  have hnp : ¬ ∃ c : UnitaryField p, x.1.rep = c • y.1.rep := by
    rintro ⟨c, hc⟩
    apply hxy; apply Subtype.ext
    rw [← Projectivization.mk_rep x.1, ← Projectivization.mk_rep y.1,
      Projectivization.mk_eq_mk_iff']
    exact ⟨c, hc.symm⟩
  exact exists_isotropic_perp_partner p x.2 (Projectivization.rep_nonzero y.1) hperp hnp

/-- **The perp-transitivity atom `hT2` is DISCHARGED** (for the only case block-triviality needs):
for isotropic points `x, y, y'` with `y, y' ⊥ x` and `⟨y,y'⟩ ≠ 0`, there is `g ∈ PSU` fixing `x` with
`g•y = y'`. Direct from the Eichler seed `exists_su_fixes_maps_nonorth`: the transvection centres
`y, y' ∈ x^⊥` automatically fix `x`. Block-triviality only ever invokes `hT2` on a non-perpendicular
pair (the separator `S` satisfies `⟨y,S⟩ ≠ 0`), so this is exactly the needed case — and `hT2` ceases
to be a hypothesis. -/
theorem psu_hT2_nonperp {x y y' : IsoPoint p n}
    (hxy : star x.1.rep ⬝ᵥ y.1.rep = 0) (hxy' : star x.1.rep ⬝ᵥ y'.1.rep = 0)
    (hyy' : star y.1.rep ⬝ᵥ y'.1.rep ≠ 0) :
    letI := psuAction p n; ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y' := by
  letI := psuAction p n
  have hyx : star y.1.rep ⬝ᵥ x.1.rep = 0 := by rw [dotProduct_star_swap, hxy, star_zero]
  have hy'x : star y'.1.rep ⬝ᵥ x.1.rep = 0 := by rw [dotProduct_star_swap, hxy', star_zero]
  obtain ⟨g, c, hc, hgy, hgx⟩ := exists_su_fixes_maps_nonorth p y.1.rep y'.1.rep x.1.rep
    y.2 y'.2 hyy' hyx hy'x
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · rw [psu_mk_smul p n g x]
    apply Subtype.ext
    rw [isoPoint_smul_coe]
    conv_lhs => rw [← Projectivization.mk_rep x.1]
    conv_rhs => rw [← Projectivization.mk_rep x.1]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, su_smul_vec_def]; exact hgx.symm⟩
  · rw [psu_mk_smul p n g y]
    apply Subtype.ext
    rw [isoPoint_smul_coe]
    conv_lhs => rw [← Projectivization.mk_rep y.1]
    conv_rhs => rw [← Projectivization.mk_rep y'.1]
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    exact ⟨c, by rw [su_smul_vec_def]; exact hgy.symm⟩

/-- **★ `PSU_n(F_{p²})` is simple** (`n ≥ 3`, `p ≥ 5`) for general `n`, reduced to just TWO atoms —
the Witt generation `hgen` and the non-perpendicular stabilizer-transitivity `hT1`. Both the
perpendicular-partner existence (`psu_hPP`) and the perpendicular transitivity in its needed case
(`psu_hT2_nonperp`) are now **theorems**, machine-checked via the Eichler seed
`exists_su_fixes_maps_nonorth` and the trace-correction partner construction. So general-`n` PSU now
needs the SAME two inputs as the `n = 3` case (`psu3_isSimpleGroup_of_generate_of_T1`): `hT2`/`hSep`
are gone. The remaining `hT1` and `hgen` are the genuine group-level Eichler/Witt-generation core. -/
theorem PSU_isSimpleGroup_of_generate_of_T1 (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤)
    (hT1 : letI := psuAction p n; ∀ {x y y' : IsoPoint p n},
      star x.1.rep ⬝ᵥ y.1.rep ≠ 0 → star x.1.rep ⬝ᵥ y'.1.rep ≠ 0 →
        ∃ g : PSUConcrete n p, g • x = x ∧ g • y = y') :
    IsSimpleGroup (PSUConcrete n p) :=
  PSU_isSimpleGroup_of_generate_of_eichler' p n hn hp hgen hT1
    (fun hxy hxy' hyy' => psu_hT2_nonperp p n hxy hxy' hyy')
    (fun hxy hperp => psu_hPP p n hxy hperp)

/-- **★★ `PSU_n(F_{p²})` is simple** (`n ≥ 3`, `p ≥ 5`), reduced to the **single** remaining atom: the
unitary Witt generation `hgen` (that the isotropic transvections generate `SU`). Every geometric
input — pretransitivity, block-triviality, the perpendicular-partner existence `hPP`, the
perpendicular transitivity `hT2`, AND the non-perpendicular stabilizer transitivity `hT1` (via the
Eichler/Siegel transformation, `psu_hT1`) — is now machine-checked, with NO Witt's-extension-theorem
appeal. Once `hgen` is discharged this becomes an unconditional proof of `IsSimpleGroup (PSU_n)`. -/
theorem PSU_isSimpleGroup_modulo_generation (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup (Fin n) (UnitaryField p) |
      ∃ (v : Fin n → UnitaryField p) (a : UnitaryField p) (hv : star v ⬝ᵥ v = 0)
        (ha : a + star a = 0), h = uTransvecSU v a hv ha} = ⊤) :
    IsSimpleGroup (PSUConcrete n p) :=
  PSU_isSimpleGroup_of_generate_of_T1 p n hn hp hgen (psu_hT1 p n)

/-- **`PSU(n,q)` is simple, modulo the two isolated geometric atoms `UExactLineTrans` +
`UExactMateTrans`** (`n ≥ 3`, `p ≥ 5`). The Witt-generation hypothesis `hgen` of
`PSU_isSimpleGroup_modulo_generation` is supplied by the genAux dimension induction
(`hgen_of_line_mate`), so PSU simplicity now reduces to exactly: exact single-vector transitivity
within `offSU C` landing in `⟨transvections⟩` (`UExactLineTrans` — the deep third-dimension torus
`exists_scale`) together with the torus-free mate step (`UExactMateTrans` — Eichler as a transvection
product). All the surrounding generation bookkeeping is machine-checked. -/
theorem PSU_isSimpleGroup_modulo_line_mate (hn : 3 ≤ n) (hp : 5 ≤ p)
    (hline : UExactLineTrans p (n := n)) (hmate : UExactMateTrans p (n := n)) :
    IsSimpleGroup (PSUConcrete n p) := by
  have h2 : (2 : UnitaryField p) ≠ 0 := by
    have h2' : ((2 : ℕ) : UnitaryField p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (UnitaryField p) p]
      intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
    simpa using h2'
  exact PSU_isSimpleGroup_modulo_generation p n hn hp (hgen_of_line_mate p h2 hline hmate)

end Iwasawa

end FiniteSimpleGroups.PSU

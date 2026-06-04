import FiniteSimpleGroups.SpAction
import FiniteSimpleGroups.SpSimple
import FiniteSimpleGroups.SpTransvection

/-!
# The Iwasawa structure for `PSp(2n,F)` — symplectic transvection subgroups

Assembling the Iwasawa criterion for `PSp(2n,F) = Sp(2n,F)/Z`, mirroring `SLnIwasawa` but on
the **symplectic** geometry. The Iwasawa family is, for a projective point `[v] ∈ ℙ²ⁿ⁻¹`, the
**long root subgroup** `spTransvecGroup v = {τ_{v,c} : c ∈ F} ≅ (F,+)` (the symplectic
transvections centered on the line `[v]`), pushed to `PSp` (`Tline`).

The "easy" Iwasawa inputs are all machine-checked elsewhere:
* `MulAction` / `FaithfulSMul`: `SpSimple.pspAction` / `pspFaithful`;
* `Nontrivial`: `SpSimple.PSp_nontrivial`;
* `is_comm`: `spTransvecGroup` is abelian (`SpTransvection`);
* `is_conj`: `spTransvecGroup_conj` (conjugation-equivariance, `SpTransvection`).

What remains are **three genuinely deep classical theorems**, disclosed here as `axiom`s (each
the symplectic analogue of an `SLn` brick or a standard structural fact), to be discharged in
later laps:
1. `sp_transvec_closure_eq_top` — symplectic transvections **generate** `Sp(2n,F)` (Eichler /
   symplectic Witt; the analogue of `transvecSL_closure_eq_top`, no mathlib infrastructure).
2. `commutator_PSp_eq_top` — `PSp(2n,F)` is **perfect** (each transvection is a commutator for
   `2 ≤ n`; needs the field-size hypothesis excluding `PSp(4,2) ≅ S₆`).
3. `pspQuasiPreprimitive` — `PSp(2n,F)` acts **quasi-preprimitively** on `ℙ²ⁿ⁻¹`. NB `Sp` is
   transitive but **not** 2-transitive (it preserves `ω`), so this needs the maximal-parabolic
   primitivity argument, not the `SLn` 2-transitivity route.

Given these three, `PSpn_isSimpleGroup_of_iwasawa` concludes `IsSimpleGroup (PSp)`.
-/

open Matrix
open scoped Pointwise commutatorElement

namespace FiniteSimpleGroups.SpN

variable {l : Type*} [DecidableEq l] [Fintype l] {F : Type*} [Field F]

/-- **First brick toward `sp_transvec_closure_eq_top`** (transitivity-on-vectors, the
non-orthogonal case): if `ω(u,w) = u ⬝ᵥ (J·w) ≠ 0`, the single transvection `τ_{w-u, 1/ω(u,w)}`
maps `u` to `w`. From `spTransvection_mulVec` (geometric action) + `spForm_self` (`ω(u,u)=0`):
`τ_{w-u,c}(u) = u + c·ω(u,w-u)·(w-u) = u + c·ω(u,w)·(w-u)`, and `c = ω(u,w)⁻¹` gives `u+(w-u)=w`.
This is the easy half of "Sp transitive on nonzero vectors"; the orthogonal case bridges
through a `z` with `ω(u,z),ω(z,w)≠0`, then generation follows by the Eichler/Witt induction. -/
theorem spTransvection_maps_of_form_ne {u w : (l ⊕ l) → F}
    (h : u ⬝ᵥ (Matrix.J l F *ᵥ w) ≠ 0) :
    spTransvection (w - u) (u ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹ *ᵥ u = w := by
  rw [spTransvection_mulVec]
  have hform : u ⬝ᵥ (Matrix.J l F *ᵥ (w - u)) = u ⬝ᵥ (Matrix.J l F *ᵥ w) := by
    rw [mulVec_sub, dotProduct_sub, spForm_self, sub_zero]
  rw [hform, inv_mul_cancel₀ h, one_smul]
  abel

/-- **Two non-zero vectors are simultaneously non-orthogonal to some vector** (over any
field): for `u, w ≠ 0` there is a `y` with `u ⬝ᵥ y ≠ 0` and `w ⬝ᵥ y ≠ 0`. Elementary — a
vector space is never the union of two proper subspaces: take standard-basis witnesses `y₁`
(for `u`) and `y₂` (for `w`); one of `y₁, y₂, y₁+y₂` avoids both kernels. Works in
characteristic 2. The kernel of "`Sp` transitive on non-zero vectors". -/
theorem exists_dotProduct_both_ne {u w : (l ⊕ l) → F} (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ y : (l ⊕ l) → F, u ⬝ᵥ y ≠ 0 ∧ w ⬝ᵥ y ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hu
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hw
  rw [Pi.zero_apply] at ha
  rw [Pi.zero_apply] at hb
  have hu1 : u ⬝ᵥ Pi.single a (1 : F) ≠ 0 := by rw [dotProduct_single, mul_one]; exact ha
  have hw2 : w ⬝ᵥ Pi.single b (1 : F) ≠ 0 := by rw [dotProduct_single, mul_one]; exact hb
  by_cases hw1 : w ⬝ᵥ Pi.single a (1 : F) = 0
  · by_cases hu2 : u ⬝ᵥ Pi.single b (1 : F) = 0
    · exact ⟨Pi.single a 1 + Pi.single b 1, by rwa [dotProduct_add, hu2, add_zero],
        by rwa [dotProduct_add, hw1, zero_add]⟩
    · exact ⟨Pi.single b 1, hu2, hw2⟩
  · exact ⟨Pi.single a 1, hu1, hw1⟩

/-- **The symplectic form is non-degenerate enough to separate a pair**: for `u, w ≠ 0`
there is a `z` with `ω(u,z) = u ⬝ᵥ (J·z) ≠ 0` and `ω(z,w) = z ⬝ᵥ (J·w) ≠ 0`. Got from
`exists_dotProduct_both_ne` by transporting along the invertible `J` (`J·z = y`, via
`J² = -1`) and the skew identity `ω(z,w) = -ω(w,z)`. The two non-orthogonality conditions
that let a single transvection move `u → z` and another move `z → w`. -/
theorem exists_form_both_ne {u w : (l ⊕ l) → F} (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ z : (l ⊕ l) → F,
      u ⬝ᵥ (Matrix.J l F *ᵥ z) ≠ 0 ∧ z ⬝ᵥ (Matrix.J l F *ᵥ w) ≠ 0 := by
  obtain ⟨y, hyu, hyw⟩ := exists_dotProduct_both_ne hu hw
  have hJz : Matrix.J l F *ᵥ (-(Matrix.J l F *ᵥ y)) = y := by
    rw [mulVec_neg, mulVec_mulVec, J_squared, neg_mulVec, one_mulVec, neg_neg]
  refine ⟨-(Matrix.J l F *ᵥ y), ?_, ?_⟩
  · rw [hJz]; exact hyu
  · rw [spForm_skew, hJz]; exact neg_ne_zero.mpr hyw

/-- **`Sp(2n,F)` is transitive on non-zero vectors, via transvections** (the orthogonal-case
bridge of the generation argument). For `u, w ≠ 0` there is a product of (at most two)
symplectic transvections — hence an element of `⨆_v spTransvecGroup v` — mapping `u` to `w`.
Pick `z` non-orthogonal to both `u` and `w` (`exists_form_both_ne`); then `τ_{z-u,·}` maps
`u → z` and `τ_{w-z,·}` maps `z → w` (`spTransvection_maps_of_form_ne`), and their product
maps `u → w`. This is the base step feeding the Witt/Eichler induction toward
`sp_transvec_closure_eq_top`. -/
theorem exists_sp_transvecGen_maps {u w : (l ⊕ l) → F} (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ g : symplecticGroup l F,
      g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧
        (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ u = w := by
  obtain ⟨z, hz1, hz2⟩ := exists_form_both_ne hu hw
  refine ⟨spTransvecSp (w - z) (z ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹
            * spTransvecSp (z - u) (u ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹, ?_, ?_⟩
  · exact mul_mem
      (le_iSup spTransvecGroup (w - z) (mem_spTransvecGroup.mpr ⟨_, rfl⟩))
      (le_iSup spTransvecGroup (z - u) (mem_spTransvecGroup.mpr ⟨_, rfl⟩))
  · have e1 : (spTransvecSp (z - u) (u ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹
        : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ u = z := by
      rw [spTransvecSp_coe]; exact spTransvection_maps_of_form_ne hz1
    have e2 : (spTransvecSp (w - z) (z ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹
        : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ z = w := by
      rw [spTransvecSp_coe]; exact spTransvection_maps_of_form_ne hz2
    rw [Submonoid.coe_mul, ← mulVec_mulVec, e1, e2]

/-- **One transvection step fixing `e`**: if `ω(a,b) ≠ 0` and `ω(e, b-a) = 0`, the single
transvection `τ_{b-a, ω(a,b)⁻¹}` lies in `⨆_v spTransvecGroup v`, **fixes `e`** (its centre
`b-a ∈ e⊥`) and **maps `a → b`**. The reusable atom of the relative-transitivity argument. -/
theorem sp_transvecFixing_step {e a b : (l ⊕ l) → F}
    (hne : a ⬝ᵥ (Matrix.J l F *ᵥ b) ≠ 0) (horth : e ⬝ᵥ (Matrix.J l F *ᵥ (b - a)) = 0) :
    ∃ t : symplecticGroup l F,
      t ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧
        (t : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e ∧
        (t : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ a = b := by
  refine ⟨spTransvecSp (b - a) (a ⬝ᵥ (Matrix.J l F *ᵥ b))⁻¹,
    le_iSup spTransvecGroup (b - a) (mem_spTransvecGroup.mpr ⟨_, rfl⟩), ?_, ?_⟩
  · rw [spTransvecSp_coe]; exact spTransvection_apply_of_orth _ horth
  · rw [spTransvecSp_coe]; exact spTransvection_maps_of_form_ne hne

/-- **Transvections fixing `e` act transitively on the hyperbolic mates of `e`** — the
relative-transitivity / stabilizer step of symplectic generation. Given `ω(e,f) = ω(e,f') = 1`
there is a product of (at most two) transvections, each **fixing `e`**, mapping `f → f'`.

Two cases, **no field-size hypothesis** (the classical small-field obstruction is dodged by
an explicit intermediate): if `ω(f,f') ≠ 0`, the single transvection `τ_{f'-f,·}` works; if
`ω(f,f') = 0`, route through `f'' = f' + e`, for which `ω(f,f'') = -1` and `ω(f'',f') = 1`
are automatically non-zero, composing two `e`-fixing transvections `f → f'' → f'`. With
`exists_sp_transvecGen_maps` (transitivity on vectors) this gives transitivity on hyperbolic
pairs — the inductive engine of `sp_transvec_closure_eq_top`. -/
theorem exists_sp_transvecFixing_maps_mate {e f f' : (l ⊕ l) → F}
    (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1) (hef' : e ⬝ᵥ (Matrix.J l F *ᵥ f') = 1) :
    ∃ g : symplecticGroup l F,
      g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧
        (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e ∧
        (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f' := by
  by_cases hff' : f ⬝ᵥ (Matrix.J l F *ᵥ f') = 0
  · -- degenerate case: route through `f'' = f' + e`
    set f'' := f' + e with hf''
    have hfe : f ⬝ᵥ (Matrix.J l F *ᵥ e) = -1 := by rw [spForm_skew, hef]
    have h1 : f ⬝ᵥ (Matrix.J l F *ᵥ f'') ≠ 0 := by
      rw [hf'', mulVec_add, dotProduct_add, hff', hfe, zero_add]; norm_num
    have h2 : f'' ⬝ᵥ (Matrix.J l F *ᵥ f') ≠ 0 := by
      rw [hf'', add_dotProduct, spForm_self f', hef', zero_add]; norm_num
    have h3 : e ⬝ᵥ (Matrix.J l F *ᵥ (f'' - f)) = 0 := by
      rw [mulVec_sub, dotProduct_sub, hf'', mulVec_add, dotProduct_add, hef', spForm_self e, hef]
      ring
    have h4 : e ⬝ᵥ (Matrix.J l F *ᵥ (f' - f'')) = 0 := by
      rw [mulVec_sub, dotProduct_sub, hf'', mulVec_add, dotProduct_add, hef', spForm_self e]
      ring
    obtain ⟨t1, ht1, ht1e, ht1f⟩ := sp_transvecFixing_step h1 h3
    obtain ⟨t2, ht2, ht2e, ht2f⟩ := sp_transvecFixing_step h2 h4
    refine ⟨t2 * t1, mul_mem ht2 ht1, ?_, ?_⟩
    · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1e, ht2e]
    · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1f, ht2f]
  · -- direct case: a single transvection `τ_{f'-f,·}`
    obtain ⟨t, ht, hte, htf⟩ := sp_transvecFixing_step hff'
      (by rw [mulVec_sub, dotProduct_sub, hef', hef, sub_self])
    exact ⟨t, ht, hte, htf⟩

/-- **`Sp(2n,F)` is transitive on hyperbolic pairs, via transvections** — the inductive
engine of symplectic generation. Given two hyperbolic pairs `(e,f)` and `(e',f')`
(`ω(e,f) = ω(e',f') = 1`) there is an element of `⨆_v spTransvecGroup v` mapping
`e → e'` and `f → f'` simultaneously.

Two moves: first map `e → e'` by `exists_sp_transvecGen_maps` (transitivity on vectors,
`e, e' ≠ 0` since `ω(·) = 1`); this carries `f` to some `t₁·f` with `ω(e', t₁·f) = ω(e,f) = 1`
(`sp_preserves_form`), a hyperbolic mate of `e'`. Then fix `e'` and map `t₁·f → f'` by
`exists_sp_transvecFixing_maps_mate`. The composite is the required transvection product.

The remaining gap to `sp_transvec_closure_eq_top` is the **dimension induction**: an element
`g ∈ Sp` agreeing with a transvection product on a hyperbolic plane `⟨e,f⟩` restricts to `Sp`
on the orthogonal complement `⟨e,f⟩⊥` (a symplectic space of dimension `2n-2`), where
transvections generate by induction and extend back. That step needs an
orthogonal-complement / restriction-of-form development not yet in scope. -/
theorem exists_sp_transvecGen_maps_pair {e f e' f' : (l ⊕ l) → F}
    (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1) (he'f' : e' ⬝ᵥ (Matrix.J l F *ᵥ f') = 1) :
    ∃ g : symplecticGroup l F,
      g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧
        (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e' ∧
        (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f' := by
  have he0 : e ≠ 0 := by rintro rfl; rw [zero_dotProduct] at hef; exact zero_ne_one hef
  have he'0 : e' ≠ 0 := by rintro rfl; rw [zero_dotProduct] at he'f'; exact zero_ne_one he'f'
  obtain ⟨t1, ht1, ht1e⟩ := exists_sp_transvecGen_maps he0 he'0
  have hmate : e' ⬝ᵥ (Matrix.J l F *ᵥ ((t1 : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f)) = 1 := by
    rw [← ht1e, sp_preserves_form t1.2 e f, hef]
  obtain ⟨t2, ht2, ht2e, ht2f⟩ := exists_sp_transvecFixing_maps_mate hmate he'f'
  refine ⟨t2 * t1, mul_mem ht2 ht1, ?_, ?_⟩
  · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1e, ht2e]
  · rw [Submonoid.coe_mul, ← mulVec_mulVec]; exact ht2f

/-- **DISCLOSED AXIOM (generation).** The symplectic transvections generate `Sp(2n,F)`:
`⨆_v {τ_{v,c} : c} = ⊤`. The symplectic analogue of `SLn.transvecSL_closure_eq_top` (which
Aristotle discharged for `SL`); mathlib has no symplectic Witt/Eichler infrastructure, so this
is a multi-lap brick. It is the Iwasawa `is_generator` input. -/
axiom sp_transvec_closure_eq_top :
    (⨆ v : (l ⊕ l) → F, spTransvecGroup v) = (⊤ : Subgroup (symplecticGroup l F))

/-- **The `PSp(2n,F)`-level transvection subgroup along the line `x`** — the image in `Sp/Z` of
`spTransvecGroup x.rep`. The Iwasawa family `T`. By `spTransvecGroup_rep`/`_smul` it depends
only on the line `x`. -/
noncomputable def Tline (x : Projectivization F ((l ⊕ l) → F)) :
    Subgroup (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) :=
  (spTransvecGroup x.rep).map (QuotientGroup.mk' (Subgroup.center _))

instance (x : Projectivization F ((l ⊕ l) → F)) : IsMulCommutative (Tline x) := by
  unfold Tline; infer_instance

theorem Tline_mk (v : (l ⊕ l) → F) (hv : v ≠ 0) :
    Tline (Projectivization.mk F v hv)
      = (spTransvecGroup v).map (QuotientGroup.mk' (Subgroup.center _)) :=
  congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center _))) (spTransvecGroup_rep v hv)

/-- **The family `Tline` generates `PSp(2n,F)`** — the Iwasawa `is_generator` obligation.
Reduces to `sp_transvec_closure_eq_top`: each `τ_{v,c}` lies in `Tline [v]` (for `v ≠ 0`) or
is `1` (for `v = 0`), so the transvections, which generate `Sp`, descend to `iSup Tline = ⊤`
in `Sp/Z`. -/
theorem Tline_iSup : iSup (Tline (l := l) (F := F)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) y
  -- the generating transvection subgroups land in `(iSup Tline).comap mk'`
  have hsub : (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ≤
      ((iSup Tline).comap (QuotientGroup.mk' (Subgroup.center (symplecticGroup l F)))
        : Subgroup (symplecticGroup l F)) := by
    refine iSup_le fun v => ?_
    intro w hw
    rw [mem_spTransvecGroup] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [Subgroup.mem_comap]
    by_cases hv : v = 0
    · -- `τ_{0,c} = 1`, trivially in any subgroup
      subst hv
      have h0 : spTransvecSp (0 : (l ⊕ l) → F) c = 1 := by
        apply Subtype.ext
        simp [spTransvecSp_coe, spTransvection]
      rw [h0, map_one]
      exact one_mem _
    · have hmem : QuotientGroup.mk' (Subgroup.center _) (spTransvecSp v c)
          ∈ Tline (Projectivization.mk F v hv) := by
        rw [Tline_mk]
        exact Subgroup.mem_map_of_mem _ (mem_spTransvecGroup.mpr ⟨c, rfl⟩)
      exact le_iSup Tline _ hmem
  have hg : g ∈ (iSup Tline).comap
      (QuotientGroup.mk' (Subgroup.center (symplecticGroup l F))) := by
    have h := hsub
    rw [sp_transvec_closure_eq_top] at h
    exact h (Subgroup.mem_top g)
  exact Subgroup.mem_comap.mp hg

/-- The **block-diagonal symplectic scaling matrix** `D(λ) = diag(λ·I, λ⁻¹·I)` on `l ⊕ l`:
it scales the `inl`-subspace by `λ` and the `inr`-subspace by `λ⁻¹`. -/
noncomputable def spDiag (lam : F) : Matrix (l ⊕ l) (l ⊕ l) F :=
  Matrix.fromBlocks (lam • 1) 0 0 (lam⁻¹ • 1)

/-- `D(λ)` is **symplectic** for `λ ≠ 0` (`D J Dᵀ = J` by block multiplication, the cross
blocks giving `(λ·1)(λ⁻¹·1) = 1`). It preserves `ω` since `ω(λx, λ⁻¹y) = ω(x,y)`. -/
theorem spDiag_mem {lam : F} (hlam : lam ≠ 0) : spDiag lam ∈ symplecticGroup l F := by
  rw [SymplecticGroup.mem_iff, spDiag, fromBlocks_transpose]
  rw [Matrix.J, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, neg_zero, mul_neg_one,
    neg_mul, transpose_smul, transpose_one, transpose_zero, smul_mul_smul_comm, Matrix.mul_one,
    mul_inv_cancel₀ hlam, inv_mul_cancel₀ hlam, one_smul]

/-- `D(λ)` scales every `inl`-supported vector by `λ`: `D(λ) ·ᵥ v = λ·v` when `v∘inr = 0`. -/
theorem spDiag_mulVec_of_inr_zero (lam : F) {v : (l ⊕ l) → F}
    (h : v ∘ Sum.inr = 0) : spDiag lam *ᵥ v = lam • v := by
  have hr : ∀ j, v (Sum.inr j) = 0 := fun j => congrFun h j
  rw [spDiag, fromBlocks_mulVec, h]
  simp only [mulVec_zero, add_zero, zero_mulVec, smul_mulVec, one_mulVec]
  ext i
  cases i with
  | inl i' => simp [Pi.smul_apply, Function.comp]
  | inr j => simp [Pi.smul_apply, hr j]

/-- **Scaling element (machine-checked).** For every non-zero `v` and non-zero scalar `λ`
there is a symplectic `g` with `g·v = λ·v`. Construction: pick an `inl`-basis vector `u`
(scaled by `λ` by the block-diagonal `D(λ)`, `spDiag_mem`/`spDiag_mulVec_of_inr_zero`) and
an `h` (a transvection product, `exists_sp_transvecGen_maps`) mapping `u → v`; then
`g = h · D(λ) · h⁻¹` scales `v` by `λ` (`g·v = h·(D·(h⁻¹·(h·u))) = h·(λ·u) = λ·v`). True over
every field, no field-size hypothesis. Replaces the former perfectness axiom entirely. -/
theorem sp_scaling_exists (v : (l ⊕ l) → F) (hv : v ≠ 0) (lam : F) (hlam : lam ≠ 0) :
    ∃ g : symplecticGroup l F, (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ v = lam • v := by
  obtain ⟨a, _⟩ := Function.ne_iff.mp hv
  obtain ⟨i₀⟩ : Nonempty l := ⟨Sum.elim id id a⟩
  set u : (l ⊕ l) → F := Pi.single (Sum.inl i₀) 1 with hu
  have hu_inr : u ∘ Sum.inr = 0 := by
    funext j
    show Pi.single (Sum.inl i₀) (1 : F) (Sum.inr j) = 0
    exact Pi.single_eq_of_ne Sum.inr_ne_inl 1
  have hu0 : u ≠ 0 := by
    intro hcon
    have h1 : u (Sum.inl i₀) = 0 := by rw [hcon]; rfl
    rw [hu, Pi.single_eq_same] at h1
    exact one_ne_zero h1
  obtain ⟨h, _, hhu⟩ := exists_sp_transvecGen_maps hu0 hv
  refine ⟨h * ⟨spDiag lam, spDiag_mem hlam⟩ * h⁻¹, ?_⟩
  have hscale : (⟨spDiag lam, spDiag_mem hlam⟩ : symplecticGroup l F) • u = lam • u := by
    rw [smul_vec_def]; exact spDiag_mulVec_of_inr_zero lam hu_inr
  have hhu' : h • u = v := hhu
  show (h * ⟨spDiag lam, spDiag_mem hlam⟩ * h⁻¹ : symplecticGroup l F) • v = lam • v
  rw [← hhu', SemigroupAction.mul_smul, SemigroupAction.mul_smul, inv_smul_smul, hscale,
    smul_comm]

/-- **Each symplectic transvection lies in the commutator subgroup** (given a scaling scalar
`λ` with `λ² ≠ 1`). For `v ≠ 0`, `τ_{v,c} = ⁅g, τ_{v, c/(λ²-1)}⁆` where `g·v = λ·v`
(`sp_scaling_exists`), by the commutator collapse `spTransvecSp_commutator`. The symplectic
analogue of `SLn.transvecSL_mem_commutator`; the `λ²≠1` hypothesis is the honest field-size
condition (it fails over `𝔽₂, 𝔽₃`, exactly where `PSp(4,q)` can fail to be simple/perfect). -/
theorem spTransvecSp_mem_commutator {v : (l ⊕ l) → F} (hv : v ≠ 0) {lam : F}
    (hlam0 : lam ≠ 0) (hlam1 : lam * lam ≠ 1) (c : F) :
    spTransvecSp v c ∈ commutator (symplecticGroup l F) := by
  obtain ⟨g, hg⟩ := sp_scaling_exists v hv lam hlam0
  have hne : lam * lam - 1 ≠ 0 := sub_ne_zero.mpr hlam1
  have hcomm : ⁅g, spTransvecSp v (c * (lam * lam - 1)⁻¹)⁆ = spTransvecSp v c := by
    rw [commutatorElement_def, spTransvecSp_commutator hg]
    congr 1
    rw [mul_comm c, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top _)

/-- **`Sp(2n,F)` is perfect** (`commutator = ⊤`) when `F` has a scalar `λ ≠ 0` with `λ² ≠ 1`
(i.e. `|F| ≥ 4`). The generating transvections (`sp_transvec_closure_eq_top`) each lie in the
commutator subgroup (`spTransvecSp_mem_commutator`), so the whole group does. Machine-checked
modulo the generation and scaling axioms — the symplectic analogue of `commutator_SLn_eq_top`. -/
theorem commutator_Sp_eq_top {lam : F} (hlam0 : lam ≠ 0) (hlam1 : lam * lam ≠ 1) :
    commutator (symplecticGroup l F) = ⊤ := by
  rw [eq_top_iff, ← sp_transvec_closure_eq_top]
  refine iSup_le fun v => ?_
  intro y hy
  rw [mem_spTransvecGroup] at hy
  obtain ⟨c, rfl⟩ := hy
  by_cases hv : v = 0
  · subst hv
    have h0 : spTransvecSp (0 : (l ⊕ l) → F) c = 1 := by
      apply Subtype.ext; simp [spTransvecSp_coe, spTransvection]
    rw [h0]; exact one_mem _
  · exact spTransvecSp_mem_commutator hv hlam0 hlam1 c

/-- **`PSp(2n,F)` is perfect** (formerly a disclosed axiom, now machine-checked modulo the
generation + scaling axioms), for `F` with a scalar `λ ≠ 0`, `λ² ≠ 1`. Descends from
`commutator_Sp_eq_top` along the surjection `Sp ↠ Sp/Z`, exactly as `commutator_PSLn_eq_top`.
The `λ²≠1` hypothesis correctly **excludes** `PSp(4,2) ≅ S₆` (not perfect) — fixing a latent
over-generality in the previous axiom. -/
theorem commutator_PSp_eq_top {lam : F} (hlam0 : lam ≠ 0) (hlam1 : lam * lam ≠ 1) :
    commutator (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) = ⊤ := by
  set G := symplecticGroup l F
  let f := QuotientGroup.mk' (Subgroup.center G)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hmap : commutator (G ⧸ Subgroup.center G) = Subgroup.map f (commutator G) := by
    show ⁅(⊤ : Subgroup _), ⊤⁆ = Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [hmap, commutator_Sp_eq_top hlam0 hlam1, Subgroup.map_top_of_surjective f hf]

/-- **DISCLOSED AXIOM (quasi-preprimitivity).** `PSp(2n,F)` acts quasi-preprimitively on
`ℙ²ⁿ⁻¹`. Unlike `SLn`, `Sp` is **not** 2-transitive (it preserves the form `ω`), so this needs
the maximal-parabolic / isotropic-line-stabilizer primitivity argument. -/
axiom pspQuasiPreprimitive [Nonempty l] :
    letI := pspAction (l := l) (F := F)
    MulAction.IsQuasiPreprimitive
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F))

/-- **The Iwasawa structure on `PSp(2n,F) ↷ ℙ²ⁿ⁻¹`** — the family `Tline` of abelian
transvection subgroups (`is_comm`), conjugation-equivariant (`is_conj`, via
`spTransvecGroup_conj` through the quotient) and generating (`is_generator`, `Tline_iSup`).
Mirrors `SLn.pslnIwasawaStructure`. -/
noncomputable def pspIwasawaStructure [Nonempty l] :
    letI := pspAction (l := l) (F := F)
    MulAction.IwasawaStructure
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) :=
  letI := pspAction (l := l) (F := F)
  { T := Tline
    is_comm := fun x => inferInstance
    is_conj := fun g x => by
      obtain ⟨g_Sp, hg⟩ := QuotientGroup.mk_surjective g
      have hne : (g_Sp : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x.rep ≠ 0 := by
        rw [← smul_vec_def]
        exact (smul_ne_zero_iff_ne g_Sp).mpr (Projectivization.rep_nonzero x)
      have hgx : g • x = Projectivization.mk F ((g_Sp : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x.rep) hne := by
        rw [← hg]
        show g_Sp • x = Projectivization.mk F ((g_Sp : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x.rep) hne
        conv_lhs => rw [← Projectivization.mk_rep x]
        rw [Projectivization.smul_mk]; rfl
      have hpar : spTransvecGroup ((g • x).rep)
          = spTransvecGroup ((g_Sp : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x.rep) := by
        have h2 : Projectivization.mk F ((g • x).rep) (Projectivization.rep_nonzero _)
            = Projectivization.mk F ((g_Sp : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x.rep) hne := by
          rw [Projectivization.mk_rep]; exact hgx
        rw [Projectivization.mk_eq_mk_iff] at h2
        obtain ⟨a, ha⟩ := h2
        rw [← ha, Units.smul_def]
        exact spTransvecGroup_smul (Units.ne_zero a) _
      rw [show (MulAut.conj g) • Tline x = (Tline x).map (MulAut.conj g) from
            Subgroup.toSubmonoid_inj.mp rfl]
      rw [Tline, Tline, hpar, ← spTransvecGroup_conj g_Sp]
      simp only [Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun z => ?_
      change (QuotientGroup.mk' (Subgroup.center _)) (g_Sp * z * g_Sp⁻¹)
          = MulAut.conj g ((QuotientGroup.mk' (Subgroup.center _)) z)
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ← hg]; rfl
    is_generator := Tline_iSup }

/-- **`PSp(2n,F) = Sp/Z` is simple** for `Nonempty l` (dimension `2n ≥ 2`) and `F` with a
scalar `λ ≠ 0`, `λ² ≠ 1` (i.e. `|F| ≥ 4`, the honest field-size condition that **excludes the
non-simple `PSp(4,2) ≅ S₆`**), **modulo the two remaining geometric axioms**
`sp_transvec_closure_eq_top` (generation) and `pspQuasiPreprimitive`, plus the elementary
`sp_scaling_exists`. Perfectness is now machine-checked (`commutator_PSp_eq_top`). The Iwasawa
criterion (`IwasawaStructure.isSimpleGroup`) applied to the faithful action on `ℙ²ⁿ⁻¹` with all
six obligations. The symplectic analogue of `SLn.PSLn_isSimpleGroup_of_rank`. -/
theorem PSpn_isSimpleGroup_of_iwasawa [Nonempty l]
    (hlam : ∃ lam : F, lam ≠ 0 ∧ lam * lam ≠ 1) :
    IsSimpleGroup (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) := by
  obtain ⟨lam, hlam0, hlam1⟩ := hlam
  letI := pspAction (l := l) (F := F)
  haveI : Nontrivial (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) :=
    PSp_nontrivial
  haveI : FaithfulSMul (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) := pspFaithful
  haveI : MulAction.IsQuasiPreprimitive
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) := pspQuasiPreprimitive
  exact pspIwasawaStructure.isSimpleGroup (commutator_PSp_eq_top hlam0 hlam1) pspFaithful

end FiniteSimpleGroups.SpN

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

What remains, after this lap's reductions, are **exactly TWO genuinely deep geometric cores**,
disclosed as `axiom`s (everything else — perfectness, the scaling element, generation's
transitivity reduction, and quasi-preprimitivity's pretransitivity — is now machine-checked):
1. `sp_stab_hyperbolic_le` — the **generation core**: a symplectic `g` fixing a hyperbolic pair
   `(e,f)` pointwise lies in `⨆_v spTransvecGroup v`. The Witt/Eichler **dimension induction**
   over the orthogonal complement `⟨e,f⟩⊥`. (`sp_transvec_closure_eq_top` reduces to this via
   machine-checked transitivity on hyperbolic pairs.)
2. `psp_isTrivialBlock_of_isBlock` — the **primitivity core**: every block of `PSp ↷ ℙ²ⁿ⁻¹` is
   trivial. `Sp` is transitive (machine-checked, `psp_isPretransitive`) but **not** 2-transitive
   (it preserves `ω`), so this needs the maximal-parabolic block argument, not the `SLn` route.
   (`pspQuasiPreprimitive` reduces to this via `IsPreprimitive → IsQuasiPreprimitive`.)

Discharged this lap (were axioms, now theorems): `commutator_PSp_eq_top` (perfectness, via the
commutator collapse `[g,τ_{v,a}]=τ_{v,(λ²-1)a}` + the now-proven `sp_scaling_exists`) and
`sp_transvec_closure_eq_top` (generation, reduced to core 1). Given the two cores,
`PSpn_isSimpleGroup_of_iwasawa [Nonempty l] (hlam : ∃ λ, λ≠0 ∧ λ²≠1)` concludes
`IsSimpleGroup (PSp)` (the `hlam`/`|F|≥4` hypothesis correctly excludes `PSp(4,2) ≅ S₆`).
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

/-- A **hyperbolic pair exists** when `l` is nonempty: an `inl`-basis vector `e = ê_{i₀}`
(non-zero) has a `ω`-mate by non-degeneracy (`exists_form_both_ne`); rescale it to `ω(e,f)=1`. -/
theorem exists_hyperbolic_pair [Nonempty l] :
    ∃ e f : (l ⊕ l) → F, e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty l›
  have he0 : (Pi.single (Sum.inl i₀) 1 : (l ⊕ l) → F) ≠ 0 := by
    intro hcon
    have h1 := congrFun hcon (Sum.inl i₀)
    rw [Pi.single_eq_same] at h1
    exact one_ne_zero h1
  obtain ⟨z, hz1, _⟩ := exists_form_both_ne he0 he0
  refine ⟨Pi.single (Sum.inl i₀) 1,
    (Pi.single (Sum.inl i₀) 1 ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹ • z, ?_⟩
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hz1]

/-! ### Building blocks for the generation core (`sp_stab_hyperbolic_le`) dimension induction -/

/-- **The pair-stabilizer preserves the orthogonal complement.** A symplectic `g` fixing `e`
and `f` maps `⟨e,f⟩⊥` into itself: if `ω(e,x)=ω(f,x)=0` then `ω(e,g·x)=ω(f,g·x)=0`. Via
`g·e=e`, `g·f=f` and `sp_preserves_form`. The "`g` restricts to `⟨e,f⟩⊥`" half of the
induction. -/
theorem sp_fixing_preserves_perp {e f : (l ⊕ l) → F} {g : symplecticGroup l F}
    (hge : (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e)
    (hgf : (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f) {x : (l ⊕ l) → F}
    (hex : e ⬝ᵥ (Matrix.J l F *ᵥ x) = 0) (hfx : f ⬝ᵥ (Matrix.J l F *ᵥ x) = 0) :
    e ⬝ᵥ (Matrix.J l F *ᵥ ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x)) = 0 ∧
      f ⬝ᵥ (Matrix.J l F *ᵥ ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x)) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [← hge, sp_preserves_form g.2 e x]; exact hex
  · rw [← hgf, sp_preserves_form g.2 f x]; exact hfx

/-- **A transvection centred in `⟨e,f⟩⊥` fixes the pair `(e,f)`.** If `ω(e,v)=ω(f,v)=0` then
`τ_{v,c}` fixes both `e` and `f` (`spTransvection_apply_of_orth`). The "extend back" half of the
induction: transvections of the complement land in the pair-stabilizer. -/
theorem spTransvection_fixes_pair {e f v : (l ⊕ l) → F} (c : F)
    (hev : e ⬝ᵥ (Matrix.J l F *ᵥ v) = 0) (hfv : f ⬝ᵥ (Matrix.J l F *ᵥ v) = 0) :
    spTransvection v c *ᵥ e = e ∧ spTransvection v c *ᵥ f = f :=
  ⟨spTransvection_apply_of_orth c hev, spTransvection_apply_of_orth c hfv⟩

/-- **Explicit projection onto the orthogonal complement `⟨e,f⟩⊥`** of a hyperbolic pair
`(e,f)`: `perpComp e f x = x + ω(f,x)·e − ω(e,x)·f`. No abstract submodule machinery — a closed
formula on the coordinate space, the foundation of the generation-core induction's complement
decomposition `V = ⟨e,f⟩ ⊕ ⟨e,f⟩⊥`. -/
noncomputable def perpComp (e f x : (l ⊕ l) → F) : (l ⊕ l) → F :=
  x + (f ⬝ᵥ (Matrix.J l F *ᵥ x)) • e - (e ⬝ᵥ (Matrix.J l F *ᵥ x)) • f

/-- `perpComp e f x` lands in `⟨e,f⟩⊥`: `ω(e, perpComp e f x) = ω(f, perpComp e f x) = 0`
(when `ω(e,f)=1`). The defining property of the complement projection. -/
theorem perpComp_mem_perp {e f : (l ⊕ l) → F} (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1)
    (x : (l ⊕ l) → F) :
    e ⬝ᵥ (Matrix.J l F *ᵥ perpComp e f x) = 0 ∧
      f ⬝ᵥ (Matrix.J l F *ᵥ perpComp e f x) = 0 := by
  have hfe : f ⬝ᵥ (Matrix.J l F *ᵥ e) = -1 := by rw [spForm_skew, hef]
  refine ⟨?_, ?_⟩
  · simp only [perpComp, mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub,
      dotProduct_smul, spForm_self, hef, smul_eq_mul, mul_zero, mul_one]
    ring
  · simp only [perpComp, mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub,
      dotProduct_smul, spForm_self, hfe, smul_eq_mul, mul_zero]
    ring

/-- The complement projection recovers `x` modulo `⟨e,f⟩`: `x = perpComp e f x − ω(f,x)·e
+ ω(e,x)·f`, i.e. `x` is the complement component plus an explicit `⟨e,f⟩`-combination. The
`V = ⟨e,f⟩ ⊕ ⟨e,f⟩⊥` decomposition, witnessed concretely. -/
theorem perpComp_add_span (e f x : (l ⊕ l) → F) :
    x = perpComp e f x - (f ⬝ᵥ (Matrix.J l F *ᵥ x)) • e + (e ⬝ᵥ (Matrix.J l F *ᵥ x)) • f := by
  simp only [perpComp]; abel

/-- **The symplectic form `ω` is non-degenerate**: if `ω(u,v) = 0` for every `v`, then `u = 0`.
Because `J` is invertible (`J² = -1`), `J·v` ranges over all vectors, reducing to the
non-degeneracy of the dot product. -/
theorem spForm_nondegenerate {u : (l ⊕ l) → F}
    (h : ∀ v, u ⬝ᵥ (Matrix.J l F *ᵥ v) = 0) : u = 0 := by
  funext i
  have hw : Matrix.J l F *ᵥ (-(Matrix.J l F *ᵥ Pi.single i 1)) = Pi.single i 1 := by
    rw [mulVec_neg, mulVec_mulVec, J_squared, neg_mulVec, one_mulVec, neg_neg]
  have hi := h (-(Matrix.J l F *ᵥ Pi.single i 1))
  rw [hw, dotProduct_single, mul_one] at hi
  exact hi

/-- **`ω` restricts non-degenerately to `⟨e,f⟩⊥`**: for `u ∈ ⟨e,f⟩⊥` non-zero (`ω(e,u)=ω(f,u)=0`),
there is a `z ∈ ⟨e,f⟩⊥` with `ω(u,z) ≠ 0`. Proof: were `ω(u,·)` zero on all of `⟨e,f⟩⊥`, then —
since `u ∈ ⟨e,f⟩⊥` makes `ω(u,e)=ω(u,f)=0` too, and `V = ⟨e,f⟩ ⊕ ⟨e,f⟩⊥` (`perpComp_add_span`,
`perpComp_mem_perp`) — `ω(u,·)` would vanish on all of `V`, forcing `u=0` (`spForm_nondegenerate`).
This is the relative non-degeneracy that powers transitivity **within** the complement (using
pair-fixing transvections) — the inductive step of the generation core. -/
theorem perp_form_ne_of_mem_perp {e f : (l ⊕ l) → F} (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1)
    {u : (l ⊕ l) → F} (hue : e ⬝ᵥ (Matrix.J l F *ᵥ u) = 0)
    (huf : f ⬝ᵥ (Matrix.J l F *ᵥ u) = 0) (hu : u ≠ 0) :
    ∃ z, e ⬝ᵥ (Matrix.J l F *ᵥ z) = 0 ∧ f ⬝ᵥ (Matrix.J l F *ᵥ z) = 0 ∧
      u ⬝ᵥ (Matrix.J l F *ᵥ z) ≠ 0 := by
  by_contra hcon
  apply hu
  apply spForm_nondegenerate
  intro x
  have hue' : u ⬝ᵥ (Matrix.J l F *ᵥ e) = 0 := by rw [spForm_skew, hue, neg_zero]
  have huf' : u ⬝ᵥ (Matrix.J l F *ᵥ f) = 0 := by rw [spForm_skew, huf, neg_zero]
  have hperp := perpComp_mem_perp hef x
  have hz : u ⬝ᵥ (Matrix.J l F *ᵥ perpComp e f x) = 0 := by
    by_contra hne
    exact hcon ⟨perpComp e f x, hperp.1, hperp.2, hne⟩
  have key : u ⬝ᵥ (Matrix.J l F *ᵥ perpComp e f x)
      = u ⬝ᵥ (Matrix.J l F *ᵥ x) + (f ⬝ᵥ (Matrix.J l F *ᵥ x)) * (u ⬝ᵥ (Matrix.J l F *ᵥ e))
        - (e ⬝ᵥ (Matrix.J l F *ᵥ x)) * (u ⬝ᵥ (Matrix.J l F *ᵥ f)) := by
    simp only [perpComp, mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  rw [hz, hue', huf', mul_zero, mul_zero, add_zero, sub_zero] at key
  exact key.symm

/-- **Relative `exists_form_both_ne` within `⟨e,f⟩⊥`**: for `u, w ∈ ⟨e,f⟩⊥` non-zero there is a
`z ∈ ⟨e,f⟩⊥` simultaneously non-orthogonal to both (`ω(u,z) ≠ 0 ∧ ω(w,z) ≠ 0`). Same proof
shape as `exists_dotProduct_both_ne` (standard-witness combination `z₁, z₂, z₁+z₂`), but the
witnesses come from the relative non-degeneracy `perp_form_ne_of_mem_perp` and lie in the
complement (a subspace, closed under `+`). The transitivity-within-complement input. -/
theorem exists_perp_form_both_ne {e f : (l ⊕ l) → F} (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1)
    {u w : (l ⊕ l) → F}
    (hue : e ⬝ᵥ (Matrix.J l F *ᵥ u) = 0) (huf : f ⬝ᵥ (Matrix.J l F *ᵥ u) = 0) (hu : u ≠ 0)
    (hwe : e ⬝ᵥ (Matrix.J l F *ᵥ w) = 0) (hwf : f ⬝ᵥ (Matrix.J l F *ᵥ w) = 0) (hw : w ≠ 0) :
    ∃ z, (e ⬝ᵥ (Matrix.J l F *ᵥ z) = 0 ∧ f ⬝ᵥ (Matrix.J l F *ᵥ z) = 0) ∧
      u ⬝ᵥ (Matrix.J l F *ᵥ z) ≠ 0 ∧ w ⬝ᵥ (Matrix.J l F *ᵥ z) ≠ 0 := by
  obtain ⟨z₁, hz1e, hz1f, hz1⟩ := perp_form_ne_of_mem_perp hef hue huf hu
  obtain ⟨z₂, hz2e, hz2f, hz2⟩ := perp_form_ne_of_mem_perp hef hwe hwf hw
  by_cases hwz1 : w ⬝ᵥ (Matrix.J l F *ᵥ z₁) = 0
  · by_cases huz2 : u ⬝ᵥ (Matrix.J l F *ᵥ z₂) = 0
    · refine ⟨z₁ + z₂,
        ⟨by rw [mulVec_add, dotProduct_add, hz1e, hz2e, add_zero],
          by rw [mulVec_add, dotProduct_add, hz1f, hz2f, add_zero]⟩, ?_, ?_⟩
      · rw [mulVec_add, dotProduct_add, huz2, add_zero]; exact hz1
      · rw [mulVec_add, dotProduct_add, hwz1, zero_add]; exact hz2
    · exact ⟨z₂, ⟨hz2e, hz2f⟩, huz2, hz2⟩
  · exact ⟨z₁, ⟨hz1e, hz1f⟩, hz1, hwz1⟩

/-- **Transitivity within `⟨e,f⟩⊥` by pair-fixing transvections** — the inductive engine of the
generation core. For `u, w ∈ ⟨e,f⟩⊥` non-zero, there is a product of transvections, **each
fixing the pair `(e,f)`** (centred in the complement) and lying in `⨆_v spTransvecGroup v`, that
maps `u → w`. Pick `z ∈ ⟨e,f⟩⊥` non-orthogonal to both (`exists_perp_form_both_ne`); then
`τ_{z-u,·}` (`u→z`) and `τ_{w-z,·}` (`z→w`) have centres `z-u, w-z ∈ ⟨e,f⟩⊥`, hence fix `(e,f)`
(`spTransvection_fixes_pair`). This is exactly transitivity-on-vectors run inside the complement,
the step that lets the dimension induction fix one more complement basis vector at a time. -/
theorem exists_perp_transvecGen_maps {e f : (l ⊕ l) → F} (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1)
    {u w : (l ⊕ l) → F}
    (hue : e ⬝ᵥ (Matrix.J l F *ᵥ u) = 0) (huf : f ⬝ᵥ (Matrix.J l F *ᵥ u) = 0) (hu : u ≠ 0)
    (hwe : e ⬝ᵥ (Matrix.J l F *ᵥ w) = 0) (hwf : f ⬝ᵥ (Matrix.J l F *ᵥ w) = 0) (hw : w ≠ 0) :
    ∃ g : symplecticGroup l F,
      g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧
        ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e ∧
          (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f) ∧
        (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ u = w := by
  obtain ⟨z, ⟨hze, hzf⟩, huz, hwz⟩ := exists_perp_form_both_ne hef hue huf hu hwe hwf hw
  have hzw : z ⬝ᵥ (Matrix.J l F *ᵥ w) ≠ 0 := by rw [spForm_skew]; exact neg_ne_zero.mpr hwz
  have hzu_e : e ⬝ᵥ (Matrix.J l F *ᵥ (z - u)) = 0 := by
    rw [mulVec_sub, dotProduct_sub, hze, hue, sub_zero]
  have hzu_f : f ⬝ᵥ (Matrix.J l F *ᵥ (z - u)) = 0 := by
    rw [mulVec_sub, dotProduct_sub, hzf, huf, sub_zero]
  have hwz_e : e ⬝ᵥ (Matrix.J l F *ᵥ (w - z)) = 0 := by
    rw [mulVec_sub, dotProduct_sub, hwe, hze, sub_zero]
  have hwz_f : f ⬝ᵥ (Matrix.J l F *ᵥ (w - z)) = 0 := by
    rw [mulVec_sub, dotProduct_sub, hwf, hzf, sub_zero]
  have ht1e : (spTransvecSp (z - u) (u ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹
      : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e := by
    rw [spTransvecSp_coe]; exact spTransvection_apply_of_orth _ hzu_e
  have ht1f : (spTransvecSp (z - u) (u ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹
      : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f := by
    rw [spTransvecSp_coe]; exact spTransvection_apply_of_orth _ hzu_f
  have ht1u : (spTransvecSp (z - u) (u ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹
      : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ u = z := by
    rw [spTransvecSp_coe]; exact spTransvection_maps_of_form_ne huz
  have ht2e : (spTransvecSp (w - z) (z ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹
      : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e := by
    rw [spTransvecSp_coe]; exact spTransvection_apply_of_orth _ hwz_e
  have ht2f : (spTransvecSp (w - z) (z ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹
      : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f := by
    rw [spTransvecSp_coe]; exact spTransvection_apply_of_orth _ hwz_f
  have ht2z : (spTransvecSp (w - z) (z ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹
      : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ z = w := by
    rw [spTransvecSp_coe]; exact spTransvection_maps_of_form_ne hzw
  refine ⟨spTransvecSp (w - z) (z ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹
            * spTransvecSp (z - u) (u ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹,
    mul_mem (le_iSup spTransvecGroup (w - z) (mem_spTransvecGroup.mpr ⟨_, rfl⟩))
      (le_iSup spTransvecGroup (z - u) (mem_spTransvecGroup.mpr ⟨_, rfl⟩)),
    ⟨?_, ?_⟩, ?_⟩
  · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1e, ht2e]
  · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1f, ht2f]
  · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1u, ht2z]

/-- **Terminal case of the generation-core induction.** If `g` fixes the pair `(e,f)` and fixes
**every** vector of `⟨e,f⟩⊥`, then `g = 1`. Because `V = ⟨e,f⟩ ⊕ ⟨e,f⟩⊥` (`perpComp_add_span`),
`g` fixes a spanning set, so `g·v = v` for all `v`, hence `g = 1` (`Matrix.mulVec_injective`).
This is what the dimension induction terminates at, once every complement vector is fixed. -/
theorem sp_eq_one_of_fixes_perp {e f : (l ⊕ l) → F} (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1)
    {g : symplecticGroup l F} (hge : (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e)
    (hgf : (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f)
    (hperp : ∀ x, e ⬝ᵥ (Matrix.J l F *ᵥ x) = 0 → f ⬝ᵥ (Matrix.J l F *ᵥ x) = 0 →
      (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x = x) :
    g = 1 := by
  have hv : ∀ v, (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ v = v := by
    intro v
    conv_lhs => rw [perpComp_add_span e f v]
    rw [mulVec_add, mulVec_sub, mulVec_smul, mulVec_smul, hge, hgf,
      hperp (perpComp e f v) (perpComp_mem_perp hef v).1 (perpComp_mem_perp hef v).2,
      ← perpComp_add_span e f v]
  apply Subtype.ext
  show (g : Matrix (l ⊕ l) (l ⊕ l) F) = 1
  refine Matrix.mulVec_injective ?_
  funext v
  rw [hv v, one_mulVec]

omit [Fintype l] in
/-- The `inl i` standard basis vector as a `Sum.elim`. -/
theorem single_inl_eq (i : l) :
    (Pi.single (Sum.inl i) 1 : (l ⊕ l) → F) = Sum.elim (Pi.single i 1) (0 : l → F) := by
  funext q
  cases q with
  | inl a => simp [Pi.single_apply, Sum.inl.injEq]
  | inr a => simp

omit [Fintype l] in
/-- The `inr i` standard basis vector as a `Sum.elim`. -/
theorem single_inr_eq (i : l) :
    (Pi.single (Sum.inr i) 1 : (l ⊕ l) → F) = Sum.elim (0 : l → F) (Pi.single i 1) := by
  funext q
  cases q with
  | inr a => simp [Pi.single_apply, Sum.inr.injEq]
  | inl a => simp

/-- `J` sends the `inl i` standard basis vector to the `inr i` one. -/
theorem J_mulVec_single_inl (i : l) :
    Matrix.J l F *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inr i) 1 := by
  rw [single_inl_eq, single_inr_eq, show Matrix.J l F = Matrix.fromBlocks 0 (-1) 1 0 from rfl,
    fromBlocks_mulVec]
  funext q
  cases q with
  | inl a => simp [one_mulVec, zero_mulVec, neg_mulVec]
  | inr a => simp [one_mulVec, Pi.single_apply, Sum.inl.injEq]

/-- `J` sends the `inr i` standard basis vector to `-(inl i)`. -/
theorem J_mulVec_single_inr (i : l) :
    Matrix.J l F *ᵥ Pi.single (Sum.inr i) 1 = - Pi.single (Sum.inl i) 1 := by
  rw [single_inr_eq, single_inl_eq, show Matrix.J l F = Matrix.fromBlocks 0 (-1) 1 0 from rfl,
    fromBlocks_mulVec]
  funext q
  cases q with
  | inl a => simp [neg_mulVec, one_mulVec, Pi.single_apply, Sum.inr.injEq]
  | inr a => simp [one_mulVec, zero_mulVec]

/-- `ω(x, single(inl i)) = x(inr i)`. -/
theorem spForm_single_inl (x : (l ⊕ l) → F) (i : l) :
    x ⬝ᵥ (Matrix.J l F *ᵥ Pi.single (Sum.inl i) 1) = x (Sum.inr i) := by
  rw [J_mulVec_single_inl, dotProduct_single, mul_one]

/-- `ω(x, single(inr i)) = -x(inl i)`. -/
theorem spForm_single_inr (x : (l ⊕ l) → F) (i : l) :
    x ⬝ᵥ (Matrix.J l F *ᵥ Pi.single (Sum.inr i) 1) = - x (Sum.inl i) := by
  rw [J_mulVec_single_inr, dotProduct_neg, dotProduct_single, mul_one]

/-- **The `offS` perp**: vectors vanishing on the `S`-coordinates `{inl i, inr i : i ∈ S}`. The
perp of the standard hyperbolic pairs indexed by `S`. -/
def offS (S : Finset l) (x : (l ⊕ l) → F) : Prop :=
  ∀ i ∈ S, x (Sum.inl i) = 0 ∧ x (Sum.inr i) = 0

omit [Fintype l] [DecidableEq l] in
theorem offS_sub {S : Finset l} {x y : (l ⊕ l) → F} (hx : offS S x) (hy : offS S y) :
    offS S (x - y) := by
  intro i hi
  refine ⟨?_, ?_⟩
  · rw [Pi.sub_apply, (hx i hi).1, (hy i hi).1, sub_zero]
  · rw [Pi.sub_apply, (hx i hi).2, (hy i hi).2, sub_zero]

omit [Fintype l] [DecidableEq l] in
theorem offS_add {S : Finset l} {x y : (l ⊕ l) → F} (hx : offS S x) (hy : offS S y) :
    offS S (x + y) := by
  intro i hi
  refine ⟨?_, ?_⟩
  · rw [Pi.add_apply, (hx i hi).1, (hy i hi).1, add_zero]
  · rw [Pi.add_apply, (hx i hi).2, (hy i hi).2, add_zero]

omit [Fintype l] in
/-- `single(inl j) ∈ offS S` when `j ∉ S`. -/
theorem offS_single_inl {S : Finset l} {j : l} (hj : j ∉ S) :
    offS S (Pi.single (Sum.inl j) 1 : (l ⊕ l) → F) := by
  intro i hi
  have hij : (Sum.inl i : l ⊕ l) ≠ Sum.inl j := fun h => hj (Sum.inl.inj h ▸ hi)
  refine ⟨by rw [Pi.single_apply, if_neg hij], by rw [Pi.single_apply, if_neg Sum.inr_ne_inl]⟩

omit [Fintype l] in
theorem offS_single_inr {S : Finset l} {j : l} (hj : j ∉ S) :
    offS S (Pi.single (Sum.inr j) 1 : (l ⊕ l) → F) := by
  intro i hi
  have hij : (Sum.inr i : l ⊕ l) ≠ Sum.inr j := fun h => hj (Sum.inr.inj h ▸ hi)
  refine ⟨by rw [Pi.single_apply, if_neg Sum.inl_ne_inr], by rw [Pi.single_apply, if_neg hij]⟩

/-- **Relative non-degeneracy in `offS S`** (direct coordinate algebra): for `x ∈ offS S`
non-zero there is `z ∈ offS S` with `ω(x,z) ≠ 0`. -/
theorem offS_form_nondeg {S : Finset l} {x : (l ⊕ l) → F} (hx : offS S x) (hx0 : x ≠ 0) :
    ∃ z, offS S z ∧ x ⬝ᵥ (Matrix.J l F *ᵥ z) ≠ 0 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hx0
  rw [Pi.zero_apply] at hp
  cases p with
  | inl j =>
    have hj : j ∉ S := fun h => hp (hx j h).1
    exact ⟨Pi.single (Sum.inr j) 1, offS_single_inr hj, by
      rw [spForm_single_inr]; exact neg_ne_zero.mpr hp⟩
  | inr j =>
    have hj : j ∉ S := fun h => hp (hx j h).2
    exact ⟨Pi.single (Sum.inl j) 1, offS_single_inl hj, by
      rw [spForm_single_inl]; exact hp⟩

/-- `ω(single(inl i), v) = -v(inr i)` (the "left" form value, via skew + `spForm_single_inl`). -/
theorem spForm_single_inl_left (v : (l ⊕ l) → F) (i : l) :
    (Pi.single (Sum.inl i) 1 : (l ⊕ l) → F) ⬝ᵥ (Matrix.J l F *ᵥ v) = - v (Sum.inr i) := by
  rw [spForm_skew, spForm_single_inl]

/-- `ω(single(inr i), v) = v(inl i)`. -/
theorem spForm_single_inr_left (v : (l ⊕ l) → F) (i : l) :
    (Pi.single (Sum.inr i) 1 : (l ⊕ l) → F) ⬝ᵥ (Matrix.J l F *ᵥ v) = v (Sum.inl i) := by
  rw [spForm_skew, spForm_single_inr, neg_neg]

/-- `offS S` characterised by `ω`-orthogonality to the standard `S`-pairs (sign-free, the form
useful for `sp_preserves_form`). -/
theorem offS_iff_form {S : Finset l} {y : (l ⊕ l) → F} : offS S y ↔ ∀ i ∈ S,
    Pi.single (Sum.inr i) 1 ⬝ᵥ (Matrix.J l F *ᵥ y) = 0 ∧
      Pi.single (Sum.inl i) 1 ⬝ᵥ (Matrix.J l F *ᵥ y) = 0 := by
  constructor
  · intro h i hi
    exact ⟨by rw [spForm_single_inr_left]; exact (h i hi).1,
      by rw [spForm_single_inl_left, (h i hi).2, neg_zero]⟩
  · intro h i hi
    refine ⟨?_, ?_⟩
    · rw [← spForm_single_inr_left y i]; exact (h i hi).1
    · have h2 := (h i hi).2; rw [spForm_single_inl_left, neg_eq_zero] at h2; exact h2

/-- **The pair-fixing predicate**: `g` fixes the standard hyperbolic pairs indexed by `S`. -/
def FixS (S : Finset l) (g : symplecticGroup l F) : Prop :=
  ∀ i ∈ S, (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1
    ∧ (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ Pi.single (Sum.inr i) 1 = Pi.single (Sum.inr i) 1

theorem FixS_mul {S : Finset l} {g h : symplecticGroup l F} (hg : FixS S g) (hh : FixS S h) :
    FixS S (g * h) := fun i hi => by
  rw [Submonoid.coe_mul]
  exact ⟨by rw [← mulVec_mulVec, (hh i hi).1, (hg i hi).1],
    by rw [← mulVec_mulVec, (hh i hi).2, (hg i hi).2]⟩

/-- A transvection centred in `offS S` fixes every `S`-pair. -/
theorem FixS_transvecSp {S : Finset l} {v : (l ⊕ l) → F} (hv : offS S v) (c : F) :
    FixS S (spTransvecSp v c) := fun i hi => by
  rw [spTransvecSp_coe]
  refine ⟨spTransvection_apply_of_orth c ?_, spTransvection_apply_of_orth c ?_⟩
  · rw [spForm_single_inl_left, (hv i hi).2, neg_zero]
  · rw [spForm_single_inr_left]; exact (hv i hi).1

/-- **A pair-fixing `g` preserves `offS S`.** Via `sp_preserves_form` (sign-free, `offS_iff_form`). -/
theorem offS_preserved {S : Finset l} {g : symplecticGroup l F} (hg : FixS S g)
    {x : (l ⊕ l) → F} (hx : offS S x) : offS S ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x) := by
  rw [offS_iff_form] at hx ⊢
  intro i hi
  refine ⟨?_, ?_⟩
  · rw [← (hg i hi).2, sp_preserves_form g.2]; exact (hx i hi).1
  · rw [← (hg i hi).1, sp_preserves_form g.2]; exact (hx i hi).2

/-- **Relative `exists_form_both_ne` in `offS S`**: for `x, w ∈ offS S` non-zero there is
`z ∈ offS S` with `ω(x,z) ≠ 0` and `ω(w,z) ≠ 0`. -/
theorem offS_form_both_ne {S : Finset l} {x w : (l ⊕ l) → F}
    (hx : offS S x) (hx0 : x ≠ 0) (hw : offS S w) (hw0 : w ≠ 0) :
    ∃ z, offS S z ∧ x ⬝ᵥ (Matrix.J l F *ᵥ z) ≠ 0 ∧ w ⬝ᵥ (Matrix.J l F *ᵥ z) ≠ 0 := by
  obtain ⟨z₁, hz1S, hz1⟩ := offS_form_nondeg hx hx0
  obtain ⟨z₂, hz2S, hz2⟩ := offS_form_nondeg hw hw0
  by_cases hwz1 : w ⬝ᵥ (Matrix.J l F *ᵥ z₁) = 0
  · by_cases hxz2 : x ⬝ᵥ (Matrix.J l F *ᵥ z₂) = 0
    · exact ⟨z₁ + z₂, offS_add hz1S hz2S,
        by rw [mulVec_add, dotProduct_add, hxz2, add_zero]; exact hz1,
        by rw [mulVec_add, dotProduct_add, hwz1, zero_add]; exact hz2⟩
    · exact ⟨z₂, hz2S, hxz2, hz2⟩
  · exact ⟨z₁, hz1S, hz1, hwz1⟩

/-- **Relative transitivity on vectors in `offS S` by pair-fixing transvections.** For
`x, w ∈ offS S` non-zero there is `g ∈ ⟨transvecs⟩` with `FixS S g` and `g·x = w`. -/
theorem offS_transvecGen_maps {S : Finset l} {x w : (l ⊕ l) → F}
    (hx : offS S x) (hx0 : x ≠ 0) (hw : offS S w) (hw0 : w ≠ 0) :
    ∃ g : symplecticGroup l F,
      g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧ FixS S g ∧
        (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x = w := by
  obtain ⟨z, hzS, hxz, hwz⟩ := offS_form_both_ne hx hx0 hw hw0
  have hzw : z ⬝ᵥ (Matrix.J l F *ᵥ w) ≠ 0 := by rw [spForm_skew]; exact neg_ne_zero.mpr hwz
  have hzx : offS S (z - x) := offS_sub hzS hx
  have hwz' : offS S (w - z) := offS_sub hw hzS
  set t1 := spTransvecSp (z - x) (x ⬝ᵥ (Matrix.J l F *ᵥ z))⁻¹ with ht1def
  set t2 := spTransvecSp (w - z) (z ⬝ᵥ (Matrix.J l F *ᵥ w))⁻¹ with ht2def
  have ht1x : (t1 : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x = z := by
    rw [ht1def, spTransvecSp_coe]; exact spTransvection_maps_of_form_ne hxz
  have ht2z : (t2 : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ z = w := by
    rw [ht2def, spTransvecSp_coe]; exact spTransvection_maps_of_form_ne hzw
  refine ⟨t2 * t1, mul_mem
    (le_iSup spTransvecGroup (w - z) (mem_spTransvecGroup.mpr ⟨_, rfl⟩))
    (le_iSup spTransvecGroup (z - x) (mem_spTransvecGroup.mpr ⟨_, rfl⟩)),
    FixS_mul (FixS_transvecSp hwz' _) (FixS_transvecSp hzx _), ?_⟩
  rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1x, ht2z]

/-- **Base case**: a symplectic `g` fixing every standard basis vector is the identity. -/
theorem sp_eq_one_of_FixS_univ {g : symplecticGroup l F} (hg : FixS Finset.univ g) : g = 1 := by
  apply Subtype.ext
  show (g : Matrix (l ⊕ l) (l ⊕ l) F) = 1
  ext q p
  have hp : (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ Pi.single p 1 = Pi.single p 1 := by
    cases p with
    | inl i => exact (hg i (Finset.mem_univ i)).1
    | inr i => exact (hg i (Finset.mem_univ i)).2
  have hentry : ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ Pi.single p 1) q
      = (g : Matrix (l ⊕ l) (l ⊕ l) F) q p := by
    rw [mulVec_single_one]; rfl
  rw [← hentry, hp, Matrix.one_apply, Pi.single_apply]

/-- Relative one-step transvection fixing `e` and the `S`-pairs (centre in `offS S`). -/
theorem offS_transvecFixing_step {S : Finset l} {e a b : (l ⊕ l) → F}
    (hba : offS S (b - a)) (hne : a ⬝ᵥ (Matrix.J l F *ᵥ b) ≠ 0)
    (horth : e ⬝ᵥ (Matrix.J l F *ᵥ (b - a)) = 0) :
    ∃ t : symplecticGroup l F, t ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧ FixS S t ∧
      (t : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e ∧ (t : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ a = b := by
  refine ⟨spTransvecSp (b - a) (a ⬝ᵥ (Matrix.J l F *ᵥ b))⁻¹,
    le_iSup spTransvecGroup (b - a) (mem_spTransvecGroup.mpr ⟨_, rfl⟩),
    FixS_transvecSp hba _, ?_, ?_⟩
  · rw [spTransvecSp_coe]; exact spTransvection_apply_of_orth _ horth
  · rw [spTransvecSp_coe]; exact spTransvection_maps_of_form_ne hne

/-- **Relative transitivity on hyperbolic mates of `e` in `offS S`** (fixing `e` and the
`S`-pairs). No field-size hypothesis (degenerate case routed through `f'' = f' + e`). -/
theorem offS_transvecFixing_maps_mate {S : Finset l} {e f f' : (l ⊕ l) → F}
    (heS : offS S e) (hfS : offS S f) (hf'S : offS S f')
    (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1) (hef' : e ⬝ᵥ (Matrix.J l F *ᵥ f') = 1) :
    ∃ g : symplecticGroup l F, g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧ FixS S g ∧
      (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e ∧ (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f' := by
  by_cases hff' : f ⬝ᵥ (Matrix.J l F *ᵥ f') = 0
  · set f'' := f' + e with hf''
    have hf''S : offS S f'' := offS_add hf'S heS
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
    obtain ⟨t1, ht1, hf1, ht1e, ht1f⟩ := offS_transvecFixing_step (offS_sub hf''S hfS) h1 h3
    obtain ⟨t2, ht2, hf2, ht2e, ht2f⟩ := offS_transvecFixing_step (offS_sub hf'S hf''S) h2 h4
    refine ⟨t2 * t1, mul_mem ht2 ht1, FixS_mul hf2 hf1, ?_, ?_⟩
    · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1e, ht2e]
    · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1f, ht2f]
  · obtain ⟨t, ht, hf1, hte, htf⟩ := offS_transvecFixing_step (offS_sub hf'S hfS) hff'
      (by rw [mulVec_sub, dotProduct_sub, hef', hef, sub_self])
    exact ⟨t, ht, hf1, hte, htf⟩

/-- **Relative transitivity on hyperbolic pairs in `offS S`** (fixing the `S`-pairs). -/
theorem offS_transvecGen_maps_pair {S : Finset l} {e f e' f' : (l ⊕ l) → F}
    (heS : offS S e) (hfS : offS S f) (he'S : offS S e') (hf'S : offS S f')
    (hef : e ⬝ᵥ (Matrix.J l F *ᵥ f) = 1) (he'f' : e' ⬝ᵥ (Matrix.J l F *ᵥ f') = 1) :
    ∃ g : symplecticGroup l F, g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) ∧ FixS S g ∧
      (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ e = e' ∧ (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f = f' := by
  have he0 : e ≠ 0 := by rintro rfl; rw [zero_dotProduct] at hef; exact zero_ne_one hef
  have he'0 : e' ≠ 0 := by rintro rfl; rw [zero_dotProduct] at he'f'; exact zero_ne_one he'f'
  obtain ⟨t1, ht1, hf1, ht1e⟩ := offS_transvecGen_maps heS he0 he'S he'0
  have ht1fS : offS S ((t1 : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f) := offS_preserved hf1 hfS
  have hmate : e' ⬝ᵥ (Matrix.J l F *ᵥ ((t1 : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ f)) = 1 := by
    rw [← ht1e, sp_preserves_form t1.2 e f, hef]
  obtain ⟨t2, ht2, hf2, ht2e, ht2f⟩ :=
    offS_transvecFixing_maps_mate he'S ht1fS hf'S hmate he'f'
  refine ⟨t2 * t1, mul_mem ht2 ht1, FixS_mul hf2 hf1, ?_, ?_⟩
  · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1e, ht2e]
  · rw [Submonoid.coe_mul, ← mulVec_mulVec]; exact ht2f

/-- **The generation induction.** Any symplectic `g` fixing the standard hyperbolic pairs
indexed by `S` lies in `⨆_v spTransvecGroup v`. Strong induction on `Sᶜ.card`: when `S ≠ univ`
peel one more standard pair `i₁ ∉ S` — map the (preserved) hyperbolic pair `(g·e_{i₁},g·f_{i₁})`
back to `(e_{i₁},f_{i₁})` by a pair-fixing transvection product `t` (so `t·g` fixes `S ∪ {i₁}`),
recurse, and `g = t⁻¹·(t·g)`. Base `S = univ`: `g` fixes every standard basis vector ⟹ `g = 1`. -/
theorem genAux_le : ∀ (n : ℕ) (S : Finset l) (g : symplecticGroup l F),
    Sᶜ.card ≤ n → FixS S g → g ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) := by
  intro n
  induction n with
  | zero =>
    intro S g hSn hg
    have hSuniv : S = Finset.univ :=
      (Finset.compl_eq_empty_iff S).mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hSn))
    subst hSuniv
    rw [sp_eq_one_of_FixS_univ hg]; exact one_mem _
  | succ n ih =>
    intro S g hSn hg
    by_cases hScard : Sᶜ.card ≤ n
    · exact ih S g hScard hg
    · have hSc : Sᶜ.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i₁, hi₁c'⟩ := hSc
      rw [Finset.mem_compl] at hi₁c'
      have heS : offS S (Pi.single (Sum.inr i₁) 1 : (l ⊕ l) → F) := offS_single_inr hi₁c'
      have hfS : offS S (Pi.single (Sum.inl i₁) 1 : (l ⊕ l) → F) := offS_single_inl hi₁c'
      have hef : (Pi.single (Sum.inr i₁) 1 : (l ⊕ l) → F) ⬝ᵥ
          (Matrix.J l F *ᵥ Pi.single (Sum.inl i₁) 1) = 1 := by
        rw [spForm_single_inl, Pi.single_eq_same]
      have he'S := offS_preserved hg heS
      have hf'S := offS_preserved hg hfS
      have he'f' : ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ Pi.single (Sum.inr i₁) 1) ⬝ᵥ
          (Matrix.J l F *ᵥ ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ Pi.single (Sum.inl i₁) 1)) = 1 := by
        rw [sp_preserves_form g.2]; exact hef
      obtain ⟨t, htmem, htfix, hte', htf'⟩ :=
        offS_transvecGen_maps_pair he'S hf'S heS hfS he'f' hef
      have hfix : FixS (insert i₁ S) (t * g) := by
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hiS
        · rw [Submonoid.coe_mul]
          exact ⟨by rw [← mulVec_mulVec]; exact htf', by rw [← mulVec_mulVec]; exact hte'⟩
        · exact (FixS_mul htfix hg) i hiS
      have hss : (insert i₁ S)ᶜ ⊂ Sᶜ := by
        rw [Finset.ssubset_iff_of_subset (Finset.compl_subset_compl.mpr (Finset.subset_insert i₁ S))]
        exact ⟨i₁, Finset.mem_compl.mpr hi₁c', by simp⟩
      have hcard : (insert i₁ S)ᶜ.card ≤ n := by
        have := Finset.card_lt_card hss; omega
      have hmem : (t * g) ∈ (⨆ v : (l ⊕ l) → F, spTransvecGroup v) :=
        ih (insert i₁ S) (t * g) hcard hfix
      have hgeq : g = t⁻¹ * (t * g) := by group
      rw [hgeq]; exact mul_mem (inv_mem htmem) hmem

/-- **The symplectic transvections generate `Sp(2n,F)`** — fully machine-checked, no
`sp_stab_hyperbolic_le` axiom. Instantiates `genAux_le` at `S = ∅`. -/
theorem sp_transvec_closure_eq_top :
    (⨆ v : (l ⊕ l) → F, spTransvecGroup v) = (⊤ : Subgroup (symplecticGroup l F)) := by
  rw [eq_top_iff]
  intro g _
  exact genAux_le (∅ : Finset l)ᶜ.card ∅ g le_rfl (fun i hi => absurd hi (Finset.notMem_empty i))

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

/-- **`PSp(2n,F)` is pretransitive on `ℙ²ⁿ⁻¹`** (machine-checked) — descends from `Sp`'s
transitivity on non-zero vectors (`exists_sp_transvecGen_maps`). For projective points `x, y`,
a transvection product maps `x.rep → y.rep`, so its image in `PSp` maps `x → y`. -/
theorem psp_isPretransitive [Nonempty l] :
    letI := pspAction (l := l) (F := F)
    MulAction.IsPretransitive
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) := by
  letI := pspAction (l := l) (F := F)
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, _, hg⟩ := exists_sp_transvecGen_maps
    (Projectivization.rep_nonzero x) (Projectivization.rep_nonzero y)
  refine ⟨QuotientGroup.mk g, ?_⟩
  show pspPermHom (QuotientGroup.mk g) x = y
  rw [pspPermHom_mk]
  show g • x = y
  conv_lhs => rw [← Projectivization.mk_rep x]
  conv_rhs => rw [← Projectivization.mk_rep y]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  exact ⟨1, by rw [one_smul]; exact ((smul_vec_def g x.rep).trans hg).symm⟩

/-! ### Primitivity: discharging the block-triviality core (`psp_isTrivialBlock_of_isBlock`)

The big primitivity axiom is reduced to the single clean **Δ₀-transitivity** statement
`sp_stab_transitive_on_perp_lines` (the stabiliser of a vector acts transitively on the
projective lines in its perp), plus machine-checked block combinatorics: T1 (non-perp
transitivity, from `exists_sp_transvecFixing_maps_mate`), the connectivity of the
non-orthogonality graph (`exists_form_both_ne`), and the rank-3 bootstrap. -/

theorem form_smul_right (a : F) (v w : (l ⊕ l) → F) :
    v ⬝ᵥ (Matrix.J l F *ᵥ (a • w)) = a * (v ⬝ᵥ (Matrix.J l F *ᵥ w)) := by
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_smul_left (a : F) (v w : (l ⊕ l) → F) :
    (a • v) ⬝ᵥ (Matrix.J l F *ᵥ w) = a * (v ⬝ᵥ (Matrix.J l F *ᵥ w)) := by
  rw [smul_dotProduct, smul_eq_mul]

/-- **Separation for the standard dot product**: for `w ≠ 0` not proportional to `u`, there is
a `t` with `u ⬝ᵥ t = 0` and `w ⬝ᵥ t ≠ 0`. Elementary 2×2-minor construction. -/
theorem exists_dot_perp_nonperp {u w : (l ⊕ l) → F} (hw : w ≠ 0)
    (hnp : ¬ ∃ a : F, w = a • u) :
    ∃ t : (l ⊕ l) → F, u ⬝ᵥ t = 0 ∧ w ⬝ᵥ t ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  rw [Pi.zero_apply] at hj
  by_cases huj : u j = 0
  · exact ⟨Pi.single j 1, by rw [dotProduct_single, mul_one]; exact huj,
      by rw [dotProduct_single, mul_one]; exact hj⟩
  · by_contra hcon
    have hcon' : ∀ t : (l ⊕ l) → F, u ⬝ᵥ t = 0 → w ⬝ᵥ t = 0 := by
      intro t ht; by_contra hwt; exact hcon ⟨t, ht, hwt⟩
    apply hnp
    refine ⟨w j * (u j)⁻¹, funext fun k => ?_⟩
    have ht : u ⬝ᵥ (Pi.single k (u j) - Pi.single j (u k)) = 0 := by
      rw [dotProduct_sub, dotProduct_single, dotProduct_single]; ring
    have hw0 := hcon' _ ht
    rw [dotProduct_sub, dotProduct_single, dotProduct_single] at hw0
    rw [Pi.smul_apply, smul_eq_mul]
    have h2 : w k * u j = w j * u k := by linear_combination hw0
    field_simp
    linear_combination h2

/-- **Perp separation for the symplectic form**: for `w ≠ 0` not proportional to `u`, there is
an `s` with `ω(u,s) = 0` and `ω(w,s) ≠ 0`. From `exists_dot_perp_nonperp` via `s = -J·t`. -/
theorem exists_form_perp_nonperp {u w : (l ⊕ l) → F} (hw : w ≠ 0)
    (hnp : ¬ ∃ a : F, w = a • u) :
    ∃ s : (l ⊕ l) → F,
      u ⬝ᵥ (Matrix.J l F *ᵥ s) = 0 ∧ w ⬝ᵥ (Matrix.J l F *ᵥ s) ≠ 0 := by
  obtain ⟨t, h1, h2⟩ := exists_dot_perp_nonperp hw hnp
  have hJ : Matrix.J l F *ᵥ (-(Matrix.J l F *ᵥ t)) = t := by
    rw [mulVec_neg, mulVec_mulVec, J_squared, neg_mulVec, one_mulVec, neg_neg]
  exact ⟨-(Matrix.J l F *ᵥ t), by rw [hJ]; exact h1, by rw [hJ]; exact h2⟩

/-- The `PSp`-action of `mk g` equals the `Sp`-action of `g` on a projective point. -/
theorem psp_mk_smul [Nonempty l] (g : symplecticGroup l F)
    (x : Projectivization F ((l ⊕ l) → F)) :
    letI := pspAction (l := l) (F := F)
    (QuotientGroup.mk g : symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) • x
      = (g : symplecticGroup l F) • x := by
  letI := pspAction (l := l) (F := F)
  show pspPermHom (QuotientGroup.mk g) x = g • x
  rw [pspPermHom_mk]; rfl

/-- `(mk g) • x` as the `mk` of `g ·ᵥ x.rep`. The workhorse for the projective block argument. -/
theorem psp_smul_eq_mk [Nonempty l] (g : symplecticGroup l F)
    (x : Projectivization F ((l ⊕ l) → F)) :
    letI := pspAction (l := l) (F := F)
    (QuotientGroup.mk g : symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) • x
      = Projectivization.mk F ((g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ x.rep)
          (by rw [← smul_vec_def]; exact (smul_ne_zero_iff_ne g).mpr x.rep_nonzero) := by
  letI := pspAction (l := l) (F := F)
  rw [psp_mk_smul]
  conv_lhs => rw [← Projectivization.mk_rep x]
  rw [Projectivization.smul_mk]
  rfl

/-- **Three-way separation for the standard dot product**: for `u, u'` neither proportional to
`v`, there is a `t` with `v ⬝ᵥ t = 0`, `u ⬝ᵥ t ≠ 0`, `u' ⬝ᵥ t ≠ 0`. From two applications of
`exists_dot_perp_nonperp` (kernel of `v ⬝ᵥ ·`) + a field-size-free combination of the witnesses. -/
theorem exists_dot_both_ne_perp {v u u' : (l ⊕ l) → F} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hunv : ¬ ∃ a : F, u = a • v) (hu'nv : ¬ ∃ a : F, u' = a • v) :
    ∃ t : (l ⊕ l) → F, v ⬝ᵥ t = 0 ∧ u ⬝ᵥ t ≠ 0 ∧ u' ⬝ᵥ t ≠ 0 := by
  obtain ⟨t1, hv1, hu1⟩ := exists_dot_perp_nonperp hu hunv
  obtain ⟨t2, hv2, hu'2⟩ := exists_dot_perp_nonperp hu' hu'nv
  by_cases hut2 : u ⬝ᵥ t2 = 0
  · by_cases hu't1 : u' ⬝ᵥ t1 = 0
    · refine ⟨t1 + t2, ?_, ?_, ?_⟩
      · rw [dotProduct_add, hv1, hv2, add_zero]
      · rw [dotProduct_add, hut2, add_zero]; exact hu1
      · rw [dotProduct_add, hu't1, zero_add]; exact hu'2
    · exact ⟨t1, hv1, hu1, hu't1⟩
  · exact ⟨t2, hv2, hut2, hu'2⟩

/-- **Relative non-degeneracy on `v^⊥`**: for `u, u'` neither proportional to `v`, there is a `w`
with `ω(v,w) = 0` (so `w ∈ v^⊥`), `ω(u,w) ≠ 0` and `ω(w,u') ≠ 0`. From `exists_dot_both_ne_perp`
via `w = -J·t`. The engine of perp-line transitivity. -/
theorem exists_form_both_ne_in_perp {v u u' : (l ⊕ l) → F} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hunv : ¬ ∃ a : F, u = a • v) (hu'nv : ¬ ∃ a : F, u' = a • v) :
    ∃ w : (l ⊕ l) → F,
      v ⬝ᵥ (Matrix.J l F *ᵥ w) = 0 ∧
      u ⬝ᵥ (Matrix.J l F *ᵥ w) ≠ 0 ∧
      w ⬝ᵥ (Matrix.J l F *ᵥ u') ≠ 0 := by
  obtain ⟨t, hvt, hut, hu't⟩ := exists_dot_both_ne_perp hu hu' hunv hu'nv
  have hJ : Matrix.J l F *ᵥ (-(Matrix.J l F *ᵥ t)) = t := by
    rw [mulVec_neg, mulVec_mulVec, J_squared, neg_mulVec, one_mulVec, neg_neg]
  refine ⟨-(Matrix.J l F *ᵥ t), ?_, ?_, ?_⟩
  · rw [hJ]; exact hvt
  · rw [hJ]; exact hut
  · rw [spForm_skew, hJ]; exact neg_ne_zero.mpr hu't

/-- **Δ₀ transitivity — perp-line Witt transitivity (machine-checked, no axiom).** The stabiliser
of a nonzero vector `v` acts transitively on the projective lines inside `v^⊥` (other than `⟨v⟩`):
for `u, u' ∈ v^⊥` nonzero, not proportional to `v`, there is `g ∈ Sp` fixing `v` (exactly) with
`g ·ᵥ u = u'`. All transvections centred in `v^⊥` fix `v` (`sp_transvecFixing_step` with `e = v`):
if `ω(u,u') ≠ 0` a single one maps `u → u'`; otherwise route through `w ∈ v^⊥` non-orthogonal to
both (`exists_form_both_ne_in_perp`). This was the last disclosed geometric axiom of the PSp
simplicity thread — it is now a theorem, so `PSpn_isSimpleGroup_of_iwasawa` is `#print axioms`
clean. (The `_hv` hypothesis is retained for the perp-line interface but unused: `u ∉ ⟨v⟩` already
forces `u ≠ 0`.) -/
theorem sp_stab_transitive_on_perp_lines {v u u' : (l ⊕ l) → F} (_hv : v ≠ 0)
    (huv : v ⬝ᵥ (Matrix.J l F *ᵥ u) = 0) (hu'v : v ⬝ᵥ (Matrix.J l F *ᵥ u') = 0)
    (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hunv : ∀ a : F, u ≠ a • v) (hu'nv : ∀ a : F, u' ≠ a • v) :
    ∃ (g : symplecticGroup l F) (c : F), c ≠ 0 ∧
      (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ v = v ∧
      (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ u = c • u' := by
  have hunv' : ¬ ∃ a : F, u = a • v := fun ⟨a, ha⟩ => hunv a ha
  have hu'nv' : ¬ ∃ a : F, u' = a • v := fun ⟨a, ha⟩ => hu'nv a ha
  by_cases huu' : u ⬝ᵥ (Matrix.J l F *ᵥ u') ≠ 0
  · have horth : v ⬝ᵥ (Matrix.J l F *ᵥ (u' - u)) = 0 := by
      rw [mulVec_sub, dotProduct_sub, hu'v, huv, sub_zero]
    obtain ⟨t, _, htv, htu⟩ := sp_transvecFixing_step huu' horth
    exact ⟨t, 1, one_ne_zero, htv, by rw [htu, one_smul]⟩
  · obtain ⟨w, hvw, huw, hwu'⟩ := exists_form_both_ne_in_perp hu hu' hunv' hu'nv'
    have horth1 : v ⬝ᵥ (Matrix.J l F *ᵥ (w - u)) = 0 := by
      rw [mulVec_sub, dotProduct_sub, hvw, huv, sub_zero]
    have horth2 : v ⬝ᵥ (Matrix.J l F *ᵥ (u' - w)) = 0 := by
      rw [mulVec_sub, dotProduct_sub, hu'v, hvw, sub_zero]
    obtain ⟨t1, _, ht1v, ht1u⟩ := sp_transvecFixing_step huw horth1
    obtain ⟨t2, _, ht2v, ht2u⟩ := sp_transvecFixing_step hwu' horth2
    refine ⟨t2 * t1, 1, one_ne_zero, ?_, ?_⟩
    · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1v, ht2v]
    · rw [Submonoid.coe_mul, ← mulVec_mulVec, ht1u, ht2u, one_smul]

/-- **T1 (non-perp transitivity, projective).** If `[y]`, `[y']` are both non-perpendicular to
`[x]`, there is `g ∈ PSp` fixing `[x]` and mapping `[y] → [y']`. -/
theorem psp_stab_maps_nonperp [Nonempty l]
    {x y y' : Projectivization F ((l ⊕ l) → F)}
    (h1 : x.rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep) ≠ 0)
    (h2 : x.rep ⬝ᵥ (Matrix.J l F *ᵥ y'.rep) ≠ 0) :
    letI := pspAction (l := l) (F := F)
    ∃ g : symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F),
      g • x = x ∧ g • y = y' := by
  letI := pspAction (l := l) (F := F)
  have hf : x.rep ⬝ᵥ (Matrix.J l F *ᵥ
      ((x.rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep))⁻¹ • y.rep)) = 1 := by
    rw [form_smul_right, inv_mul_cancel₀ h1]
  have hf' : x.rep ⬝ᵥ (Matrix.J l F *ᵥ
      ((x.rep ⬝ᵥ (Matrix.J l F *ᵥ y'.rep))⁻¹ • y'.rep)) = 1 := by
    rw [form_smul_right, inv_mul_cancel₀ h2]
  obtain ⟨g, _, hgx, hgy⟩ := exists_sp_transvecFixing_maps_mate hf hf'
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · rw [psp_smul_eq_mk]
    conv_rhs => rw [← Projectivization.mk_rep x]
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul]; exact hgx.symm⟩
  · rw [psp_smul_eq_mk]
    have hgyrep : (g : Matrix (l ⊕ l) (l ⊕ l) F) *ᵥ y.rep
        = ((x.rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep)) *
            (x.rep ⬝ᵥ (Matrix.J l F *ᵥ y'.rep))⁻¹) • y'.rep := by
      have hthis := hgy
      rw [mulVec_smul] at hthis
      have h3 := congrArg (fun z => (x.rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep)) • z) hthis
      -- v4.31 (cookbook I): the `congrArg` redex is already β-reduced at elaboration; the old
      -- `simp only at h3` is now a no-op error, so it is dropped.
      rw [smul_smul, mul_inv_cancel₀ h1, one_smul, smul_smul] at h3
      exact h3
    conv_rhs => rw [← Projectivization.mk_rep y']
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨_, hgyrep.symm⟩

/-- **T2 (perp transitivity, projective).** From the Δ₀ axiom: if `[y]`, `[y']` are both
perpendicular to `[x]` and distinct from `[x]`, there is `g ∈ PSp` fixing `[x]` mapping
`[y] → [y']`. -/
theorem psp_stab_maps_perp [Nonempty l]
    {x y y' : Projectivization F ((l ⊕ l) → F)}
    (hxy : x.rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep) = 0)
    (hxy' : x.rep ⬝ᵥ (Matrix.J l F *ᵥ y'.rep) = 0)
    (hyx : y ≠ x) (hy'x : y' ≠ x) :
    letI := pspAction (l := l) (F := F)
    ∃ g : symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F),
      g • x = x ∧ g • y = y' := by
  letI := pspAction (l := l) (F := F)
  have hunv : ∀ a : F, y.rep ≠ a • x.rep := by
    intro a hcon; apply hyx
    rw [← Projectivization.mk_rep y, ← Projectivization.mk_rep x, Projectivization.mk_eq_mk_iff']
    exact ⟨a, hcon.symm⟩
  have hu'nv : ∀ a : F, y'.rep ≠ a • x.rep := by
    intro a hcon; apply hy'x
    rw [← Projectivization.mk_rep y', ← Projectivization.mk_rep x, Projectivization.mk_eq_mk_iff']
    exact ⟨a, hcon.symm⟩
  obtain ⟨g, c, _, hgx, hgy⟩ := sp_stab_transitive_on_perp_lines x.rep_nonzero hxy hxy'
    y.rep_nonzero y'.rep_nonzero hunv hu'nv
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · rw [psp_smul_eq_mk]
    conv_rhs => rw [← Projectivization.mk_rep x]
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul]; exact hgx.symm⟩
  · rw [psp_smul_eq_mk]
    conv_rhs => rw [← Projectivization.mk_rep y']
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨c, hgy.symm⟩

/-- Scaling bridge: the form value at `[(mk w)]` (right slot) is a nonzero multiple of the value
at `w`. -/
theorem form_rep_mk_right_smul (x : Projectivization F ((l ⊕ l) → F)) {w : (l ⊕ l) → F}
    (hw : w ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ x.rep ⬝ᵥ (Matrix.J l F *ᵥ (Projectivization.mk F w hw).rep)
        = a * (x.rep ⬝ᵥ (Matrix.J l F *ᵥ w)) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F w hw
  exact ⟨a, a.ne_zero, by rw [← ha, Units.smul_def, form_smul_right]⟩

/-- Scaling bridge: the form value at `[(mk w)]` (left slot) is a nonzero multiple of the value
at `w`. -/
theorem form_rep_mk_left_smul {w : (l ⊕ l) → F} (hw : w ≠ 0)
    (y : Projectivization F ((l ⊕ l) → F)) :
    ∃ a : F, a ≠ 0 ∧ (Projectivization.mk F w hw).rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep)
        = a * (w ⬝ᵥ (Matrix.J l F *ᵥ y.rep)) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F w hw
  exact ⟨a, a.ne_zero, by rw [← ha, Units.smul_def, form_smul_left]⟩

/-- **Block expansion via a non-perpendicular partner.** If `q, p' ∈ B` are non-perpendicular
and `w` is any point non-perpendicular to `q`, then `w ∈ B`. The atom of the connectivity
argument: `Stab([q])` is transitive on points non-perp to `[q]` (T1), and `B` is `Stab([q])`-
invariant since `q ∈ B`. -/
theorem block_mem_of_nonperp [Nonempty l]
    {B : Set (Projectivization F ((l ⊕ l) → F))}
    (hB : letI := pspAction (l := l) (F := F);
      MulAction.IsBlock (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) B)
    {q p' w : Projectivization F ((l ⊕ l) → F)} (hq : q ∈ B) (hp' : p' ∈ B)
    (hqp' : q.rep ⬝ᵥ (Matrix.J l F *ᵥ p'.rep) ≠ 0)
    (hqw : q.rep ⬝ᵥ (Matrix.J l F *ᵥ w.rep) ≠ 0) :
    w ∈ B := by
  letI := pspAction (l := l) (F := F)
  obtain ⟨g, hgq, hgp'⟩ := psp_stab_maps_nonperp hqp' hqw
  have hgB : g • B = B := hB.smul_eq_of_mem hq (by rw [hgq]; exact hq)
  rw [← hgp', ← hgB]
  exact Set.smul_mem_smul_set hp'

/-- **Step 2 — a block with a non-perpendicular pair is everything.** Connectivity of the
non-orthogonality graph (diameter `≤ 2`, `exists_form_both_ne`) plus `block_mem_of_nonperp`. -/
theorem block_univ_of_nonperp_pair [Nonempty l]
    {B : Set (Projectivization F ((l ⊕ l) → F))}
    (hB : letI := pspAction (l := l) (F := F);
      MulAction.IsBlock (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) B)
    {p r : Projectivization F ((l ⊕ l) → F)} (hp : p ∈ B) (hr : r ∈ B)
    (hpr : p.rep ⬝ᵥ (Matrix.J l F *ᵥ r.rep) ≠ 0) :
    B = Set.univ := by
  letI := pspAction (l := l) (F := F)
  rw [Set.eq_univ_iff_forall]
  intro t
  by_cases hpt : p.rep ⬝ᵥ (Matrix.J l F *ᵥ t.rep) ≠ 0
  · exact block_mem_of_nonperp hB hp hr hpr hpt
  · have hpt0 : p.rep ⬝ᵥ (Matrix.J l F *ᵥ t.rep) = 0 := not_not.mp hpt
    obtain ⟨z, hz1, hz2⟩ := exists_form_both_ne p.rep_nonzero t.rep_nonzero
    have hz0 : z ≠ 0 := by rintro rfl; rw [mulVec_zero, dotProduct_zero] at hz1; exact hz1 rfl
    set Z := Projectivization.mk F z hz0 with hZ
    obtain ⟨a, ha0, haeq⟩ := form_rep_mk_right_smul p hz0
    have hpZ : p.rep ⬝ᵥ (Matrix.J l F *ᵥ Z.rep) ≠ 0 := by
      rw [hZ, haeq]; exact mul_ne_zero ha0 hz1
    have hZB : Z ∈ B := block_mem_of_nonperp hB hp hr hpr hpZ
    -- now Z non-perp to t : Z.rep ⬝ᵥ J t.rep ≠ 0
    obtain ⟨b, hb0, hbeq⟩ := form_rep_mk_left_smul hz0 t
    have hZt : Z.rep ⬝ᵥ (Matrix.J l F *ᵥ t.rep) ≠ 0 := by
      rw [hZ, hbeq]; exact mul_ne_zero hb0 hz2
    -- and Z non-perp to p : Z.rep ⬝ᵥ J p.rep ≠ 0  (skew of hpZ)
    have hZp : Z.rep ⬝ᵥ (Matrix.J l F *ᵥ p.rep) ≠ 0 := by
      rw [spForm_skew]; exact neg_ne_zero.mpr hpZ
    exact block_mem_of_nonperp hB hZB hp hZp hZt

/-- **Primitivity core, discharged modulo the Δ₀ axiom.** Every block of `PSp(2n,F)` on
`ℙ²ⁿ⁻¹` is trivial. If the block is not a subsingleton, take two distinct points; a non-perp
pair (directly, or produced via the Δ₀ axiom `psp_stab_maps_perp` + `exists_form_perp_nonperp`
in the perp case) forces the block to be everything (`block_univ_of_nonperp_pair`). -/
theorem psp_isTrivialBlock_of_isBlock [Nonempty l] :
    letI := pspAction (l := l) (F := F)
    ∀ {B : Set (Projectivization F ((l ⊕ l) → F))},
      MulAction.IsBlock (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) B →
        MulAction.IsTrivialBlock B := by
  letI := pspAction (l := l) (F := F)
  intro B hB
  by_cases hs : B.Subsingleton
  · exact Or.inl hs
  · right
    rw [Set.not_subsingleton_iff] at hs
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    by_cases hxyperp : x.rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep) ≠ 0
    · exact block_univ_of_nonperp_pair hB hx hy hxyperp
    · have hxy0 : x.rep ⬝ᵥ (Matrix.J l F *ᵥ y.rep) = 0 := not_not.mp hxyperp
      have hnp : ¬ ∃ a : F, y.rep = a • x.rep := by
        rintro ⟨a, ha⟩; apply hxy; symm
        rw [← Projectivization.mk_rep y, ← Projectivization.mk_rep x,
          Projectivization.mk_eq_mk_iff']
        exact ⟨a, ha.symm⟩
      obtain ⟨s, hs1, hs2⟩ := exists_form_perp_nonperp y.rep_nonzero hnp
      have hs0 : s ≠ 0 := by rintro rfl; rw [mulVec_zero, dotProduct_zero] at hs2; exact hs2 rfl
      set S := Projectivization.mk F s hs0 with hS
      -- S ≠ x (else ω(y,s)=0)
      have hSx : S ≠ x := by
        rw [hS]
        intro hcon
        rw [← Projectivization.mk_rep x, Projectivization.mk_eq_mk_iff'] at hcon
        obtain ⟨b, hb⟩ := hcon
        -- hb : b • x.rep = s ; then ω(y,s) = b • ω(y,x.rep) = -b • ω(x,y) = 0
        rw [← hb, form_smul_right, spForm_skew, hxy0, neg_zero, mul_zero] at hs2
        exact hs2 rfl
      -- ω(x, S.rep) = 0
      obtain ⟨a, ha0, haeq⟩ := form_rep_mk_right_smul x hs0
      have hxS : x.rep ⬝ᵥ (Matrix.J l F *ᵥ S.rep) = 0 := by rw [hS, haeq, hs1, mul_zero]
      -- map y → S within Stab(x): S ∈ B
      obtain ⟨g, hgx, hgy⟩ := psp_stab_maps_perp hxy0 hxS hxy.symm hSx
      have hgB : g • B = B := hB.smul_eq_of_mem hx (by rw [hgx]; exact hx)
      have hSB : S ∈ B := by rw [← hgy, ← hgB]; exact Set.smul_mem_smul_set hy
      -- ω(y, S.rep) ≠ 0 : non-perp pair (y, S)
      obtain ⟨a', ha'0, ha'eq⟩ := form_rep_mk_right_smul y hs0
      have hyS : y.rep ⬝ᵥ (Matrix.J l F *ᵥ S.rep) ≠ 0 := by
        rw [hS, ha'eq]; exact mul_ne_zero ha'0 hs2
      exact block_univ_of_nonperp_pair hB hy hSB hyS

/-- **`PSp(2n,F)` acts preprimitively on `ℙ²ⁿ⁻¹`** — pretransitivity machine-checked
(`psp_isPretransitive`), block-triviality the disclosed core (`psp_isTrivialBlock_of_isBlock`). -/
theorem pspPreprimitive [Nonempty l] :
    letI := pspAction (l := l) (F := F)
    MulAction.IsPreprimitive
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) :=
  letI := pspAction (l := l) (F := F)
  { toIsPretransitive := psp_isPretransitive
    isTrivialBlock_of_isBlock := psp_isTrivialBlock_of_isBlock }

/-- **`PSp(2n,F)` acts quasi-preprimitively on `ℙ²ⁿ⁻¹`** — the Iwasawa obligation, now resting
only on the primitivity-core axiom `psp_isTrivialBlock_of_isBlock` (pretransitivity is proven).
From `IsPreprimitive` via the mathlib instance `IsPreprimitive.isQuasiPreprimitive`. -/
theorem pspQuasiPreprimitive [Nonempty l] :
    letI := pspAction (l := l) (F := F)
    MulAction.IsQuasiPreprimitive
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) :=
  letI := pspAction (l := l) (F := F)
  haveI := pspPreprimitive (l := l) (F := F)
  inferInstance

omit [Fintype l] in
/-- **`ℙ²ⁿ⁻¹(F)` is nontrivial** for `Nonempty l` (dimension `2n ≥ 2`): the projective points
`[ê_{inl i₀}]` and `[ê_{inr i₀}]` are distinct (different support ⇒ not scalar multiples). -/
theorem projectivization_nontrivial [Nonempty l] :
    Nontrivial (Projectivization F ((l ⊕ l) → F)) := by
  obtain ⟨i₀⟩ := ‹Nonempty l›
  have h1 : (Pi.single (Sum.inl i₀) 1 : (l ⊕ l) → F) ≠ 0 := by
    intro hc; have h := congrFun hc (Sum.inl i₀)
    rw [Pi.single_eq_same] at h; exact one_ne_zero h
  have h2 : (Pi.single (Sum.inr i₀) 1 : (l ⊕ l) → F) ≠ 0 := by
    intro hc; have h := congrFun hc (Sum.inr i₀)
    rw [Pi.single_eq_same] at h; exact one_ne_zero h
  refine ⟨Projectivization.mk F _ h1, Projectivization.mk F _ h2, ?_⟩
  intro heq
  rw [Projectivization.mk_eq_mk_iff] at heq
  obtain ⟨a, ha⟩ := heq
  have hc := congrFun ha (Sum.inl i₀)
  rw [Pi.smul_apply, Pi.single_eq_of_ne Sum.inl_ne_inr 1, smul_zero, Pi.single_eq_same] at hc
  exact one_ne_zero hc.symm

/-- **Primitivity core in maximal-stabilizer form.** `PSp ↷ ℙ²ⁿ⁻¹` is preprimitive **iff** the
stabilizer of a point is a maximal subgroup (the maximal-parabolic criterion). Equivalent to
`psp_isTrivialBlock_of_isBlock`; this is the recognized textbook target for the remaining
primitivity work (point-stabilizer of a projective line = a maximal parabolic). Machine-checked
from pretransitivity (`psp_isPretransitive`) + nontriviality via Wielandt th. 7.5
(`MulAction.isCoatom_stabilizer_iff_preprimitive`). -/
theorem pspPreprimitive_iff_isCoatom_stabilizer [Nonempty l]
    (a : Projectivization F ((l ⊕ l) → F)) :
    letI := pspAction (l := l) (F := F)
    IsCoatom (MulAction.stabilizer
        (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) a) ↔
      MulAction.IsPreprimitive
        (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
        (Projectivization F ((l ⊕ l) → F)) := by
  letI := pspAction (l := l) (F := F)
  haveI := psp_isPretransitive (l := l) (F := F)
  haveI := projectivization_nontrivial (l := l) (F := F)
  exact MulAction.isCoatom_stabilizer_iff_preprimitive
    (G := symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) (a := a)

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
theorem PSpn_isSimpleGroup_of_perfect [Nonempty l]
    (hperf : commutator (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) = ⊤) :
    IsSimpleGroup (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) := by
  letI := pspAction (l := l) (F := F)
  haveI : Nontrivial (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) :=
    PSp_nontrivial
  haveI : FaithfulSMul (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) := pspFaithful
  haveI : MulAction.IsQuasiPreprimitive
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) := pspQuasiPreprimitive
  exact pspIwasawaStructure.isSimpleGroup hperf pspFaithful

theorem PSpn_isSimpleGroup_of_iwasawa [Nonempty l]
    (hlam : ∃ lam : F, lam ≠ 0 ∧ lam * lam ≠ 1) :
    IsSimpleGroup (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) := by
  obtain ⟨lam, hlam0, hlam1⟩ := hlam
  exact PSpn_isSimpleGroup_of_perfect (commutator_PSp_eq_top hlam0 hlam1)

end FiniteSimpleGroups.SpN

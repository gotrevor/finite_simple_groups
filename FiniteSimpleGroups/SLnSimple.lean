import FiniteSimpleGroups.SLnAction
import FiniteSimpleGroups.SLnPerfect

/-!
# Toward `PSL(n,F)` simplicity for `n ≥ 3` via Iwasawa — the `ℙ^{n-1}` action descent

`SLnPerfect.lean` discharged the first two Iwasawa obligations for
`PSL_isSimpleGroup_rank_ge_three` (perfect, nontrivial). The remaining obligations
(`MulAction`, `FaithfulSMul`, `IsQuasiPreprimitive`, `IwasawaStructure`) all live on
the action of `PSL(n,F)` on the projective space `ℙ^{n-1}(F) = Projectivization F (n → F)`.

This file builds that action by descending the linear `SL(n,F)`-action (from
`SLnAction.lean`) through the center, exactly as `SL2.lean` does for `n = 2`/`ℙ¹`
— but **for general `n`**, so the same development covers every rank:

* `center_smul_eq` : the center of `SL(n,F)` (the scalar matrices) acts trivially on
  `ℙ^{n-1}` (a scalar `r ≠ 0` sends `v` to the same line). Generalizes `SL2.center_smul_eq`
  (which only had the `±1` center) using mathlib's `SpecialLinearGroup.mem_center_iff`.
* `center_le_ker` : hence the center lies in the kernel of the permutation action.
* `pslnPermHom` / `pslnAction` : the descended representation `PSL(n,F) → Sym(ℙ^{n-1})`
  and the resulting `MulAction (PSL = SL/Z) ℙ^{n-1}` — the Iwasawa `MulAction` obligation.

`pslnAction`/`pslnPermHom` are kept as `def`s (not global `instance`s): the general
quotient type `SL n F ⧸ center` specialises at `(Fin 2, ZMod q)` to `SL2.psl1Action`'s
type, so registering a global instance here would diamond with it.
-/

open Matrix Module

namespace FiniteSimpleGroups.SLn

variable {n : Type*} [DecidableEq n] [Fintype n] {F : Type*} [Field F]

/-- **The center of `SL(n,F)` acts trivially on `ℙ^{n-1}(F)`.** A central element is a
scalar matrix `scalar n r` with `r^{|n|} = 1` (mathlib `SpecialLinearGroup.mem_center_iff`);
`r ≠ 0`, so `r • v` and `v` span the same line. -/
theorem center_smul_eq {z : SpecialLinearGroup n F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup n F))
    (x : Projectivization F (n → F)) : z • x = x := by
  obtain ⟨r, hrpow, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  induction x using Projectivization.ind with
  | h v hv =>
    -- a nonzero vector forces `n` nonempty, hence `|n| > 0`, hence `r ≠ 0`
    have hne : Nonempty n := by
      by_contra h; rw [not_nonempty_iff] at h; exact hv (Subsingleton.elim v 0)
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0, zero_pow Fintype.card_pos.ne'] at hrpow; exact zero_ne_one hrpow
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 r hr0, ?_⟩
    show (Units.mk0 r hr0 : F) • v = z • v
    rw [smul_vec_def, ← hr, Units.val_mk0]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- The center of `SL(n,F)` lies in the kernel of the permutation action on `ℙ^{n-1}`. -/
theorem center_le_ker :
    Subgroup.center (SpecialLinearGroup n F) ≤
      (MulAction.toPermHom (SpecialLinearGroup n F)
        (Projectivization F (n → F))).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  ext x
  simpa using center_smul_eq hz x

/-- The descended permutation representation `PSL(n,F) = SL/Z → Sym(ℙ^{n-1})`. Faithfulness
(injectivity) is the next Iwasawa obligation; here we only build the hom. -/
noncomputable def pslnPermHom :
    (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F)) →*
      Equiv.Perm (Projectivization F (n → F)) :=
  QuotientGroup.lift (Subgroup.center _)
    (MulAction.toPermHom (SpecialLinearGroup n F) (Projectivization F (n → F)))
    center_le_ker

/-- **`PSL(n,F)` acts on `ℙ^{n-1}(F)`** — the Iwasawa `MulAction` obligation, descended
from `SL(n,F)` through the center (`center_smul_eq`). Generalizes `SL2.psl1Action` to all
ranks. Kept as a `def` (not a global `instance`) to avoid an instance diamond with the
`n = 2` instance `SL2.psl1Action`. -/
@[reducible]
noncomputable def pslnAction :
    MulAction (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) :=
  MulAction.compHom _ pslnPermHom

/-! ### Faithfulness of the `PSL(n,F)` action — the Iwasawa `FaithfulSMul` obligation

The kernel of the `SL(n,F)` action on `ℙ^{n-1}` is **exactly** the center: `center_le_ker`
gives `⊇`; the reverse `ker_le_center` is the content here, namely that an element fixing
every line is a scalar (hence central). So the descended representation `pslnPermHom :
PSL(n,F) → Sym(ℙ^{n-1})` is injective. This generalizes `SL2.mem_center_of_smul_eq` /
`SL2.pslPermHom_injective` to all ranks. The "every nonzero vector is an eigenvector ⟹ the
matrix is scalar" argument is run on the standard basis: each `e_i` forces column `i` to be
`a_i · e_i` (off-diagonal entries vanish), and each `e_i + e_{i₀}` forces `a_i = a_{i₀}`. -/

/-- If `g` fixes the line `[v]` (for `v ≠ 0`), then `g.mulVec v` is a scalar multiple of `v`
(the geometric meaning of "fixes the line"). -/
theorem parallel_of_fixes (g : SpecialLinearGroup n F)
    (h : ∀ x : Projectivization F (n → F), g • x = x)
    (v : n → F) (hv : v ≠ 0) :
    ∃ a : Fˣ, (a : F) • v = g.val.mulVec v := by
  have hx := h (Projectivization.mk _ v hv)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by
    rw [show g.val.mulVec v = g • v from (smul_vec_def g v).symm, ← Units.smul_def]; exact ha⟩

/-- **An `SL(n,F)` element fixing every line of `ℙ^{n-1}` is central** (a scalar matrix). The
crux of faithfulness: `ker (SL ↠ Sym ℙ^{n-1}) ≤ center`. Every nonzero vector is an
eigenvector of `g`; testing the standard basis `e_i` (columns are `a_i · e_i`, so `g` is
diagonal) and the vectors `e_i + e_{i₀}` (forcing all `a_i` equal) shows `g = scalar (a_{i₀})`,
which has `det = a_{i₀}^{|n|} = 1`, hence lies in the center (`SpecialLinearGroup.mem_center_iff`). -/
theorem mem_center_of_smul_eq [Nonempty n] (g : SpecialLinearGroup n F)
    (h : ∀ x : Projectivization F (n → F), g • x = x) :
    g ∈ Subgroup.center (SpecialLinearGroup n F) := by
  -- column `i` of `g` is `a i • e_i`
  have col : ∀ i : n, ∃ a : Fˣ, ∀ j, g.val j i = (a : F) * (Pi.single i 1 : n → F) j := by
    intro i
    have hsi : (Pi.single i 1 : n → F) ≠ 0 := fun hz => by simpa using congrFun hz i
    obtain ⟨a, ha⟩ := parallel_of_fixes g h (Pi.single i 1) hsi
    refine ⟨a, fun j => ?_⟩
    have e := congrFun ha j
    rw [mulVec_single_one] at e
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at e
    exact e.symm
  choose a ha using col
  have hoff : ∀ i j : n, j ≠ i → g.val j i = 0 := fun i j hji => by
    rw [ha i j, Pi.single_eq_of_ne hji, mul_zero]
  have hdiagval : ∀ i : n, g.val i i = (a i : F) := fun i => by
    rw [ha i i, Pi.single_eq_same, mul_one]
  obtain ⟨i0⟩ := (inferInstance : Nonempty n)
  -- all diagonal entries agree
  have hAllEq : ∀ i : n, (a i : F) = (a i0 : F) := by
    intro i
    by_cases hi : i = i0
    · rw [hi]
    · have hw : (Pi.single i 1 + Pi.single i0 1 : n → F) ≠ 0 := fun hz => by
        have := congrFun hz i
        rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hi, add_zero] at this
        exact one_ne_zero this
      obtain ⟨b, hb⟩ := parallel_of_fixes g h _ hw
      have ei := congrFun hb i
      have ei0 := congrFun hb i0
      rw [Matrix.mulVec_add, mulVec_single_one, mulVec_single_one] at ei ei0
      have lhsi : ((b : F) • (Pi.single i 1 + Pi.single i0 1 : n → F)) i = (b : F) := by
        simp [Pi.single_eq_same, Pi.single_eq_of_ne hi]
      have lhsi0 : ((b : F) • (Pi.single i 1 + Pi.single i0 1 : n → F)) i0 = (b : F) := by
        simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi)]
      have rhsi : (g.val.col i + g.val.col i0) i = (a i : F) := by
        simp only [Pi.add_apply, Matrix.col_apply]
        rw [hdiagval i, hoff i0 i hi, add_zero]
      have rhsi0 : (g.val.col i + g.val.col i0) i0 = (a i0 : F) := by
        simp only [Pi.add_apply, Matrix.col_apply]
        rw [hdiagval i0, hoff i i0 (Ne.symm hi), zero_add]
      rw [lhsi, rhsi] at ei
      rw [lhsi0, rhsi0] at ei0
      rw [← ei, ← ei0]
  -- assemble: `g = scalar (a i0)`, central
  set r : F := (a i0 : F) with hrdef
  have hscalar : Matrix.scalar n r = g.val := by
    ext i j
    rw [Matrix.scalar_apply]
    by_cases hij : i = j
    · subst hij; rw [diagonal_apply_eq, hdiagval i, hAllEq i]
    · rw [diagonal_apply_ne _ hij, hoff j i hij]
  have hdet : r ^ Fintype.card n = 1 := by
    have h1 : Matrix.det (Matrix.scalar n r) = 1 := by rw [hscalar]; exact g.2
    rwa [show (Matrix.scalar n r) = diagonal (fun _ => r) from rfl, det_diagonal,
      Finset.prod_const, Finset.card_univ] at h1
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨r, hdet, hscalar⟩

/-- **The kernel of the `ℙ^{n-1}` action equals the center** — with `center_le_ker`, this
pins `ker (toPermHom) = center`. -/
theorem ker_le_center [Nonempty n] :
    (MulAction.toPermHom (SpecialLinearGroup n F)
      (Projectivization F (n → F))).ker ≤
      Subgroup.center (SpecialLinearGroup n F) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  apply mem_center_of_smul_eq g
  intro x
  have := (Equiv.ext_iff.mp hg) x
  simpa using this

theorem pslnPermHom_mk (g : SpecialLinearGroup n F) :
    pslnPermHom (QuotientGroup.mk g) =
      MulAction.toPermHom (SpecialLinearGroup n F) (Projectivization F (n → F)) g := rfl

/-- **`pslnPermHom : PSL(n,F) → Sym(ℙ^{n-1})` is injective** — its kernel is
`ker (toPermHom) / center = ⊥` because `ker (toPermHom) = center` (`ker_le_center`). This
is the Iwasawa `FaithfulSMul` obligation in representation form (`PSL(n,F)` acts faithfully
on `ℙ^{n-1}`). Generalizes `SL2.pslPermHom_injective` to all ranks. -/
theorem pslnPermHom_injective [Nonempty n] :
    Function.Injective (pslnPermHom (n := n) (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [pslnPermHom_mk] at hx
    exact (QuotientGroup.eq_one_iff g).mpr (ker_le_center (MonoidHom.mem_ker.mpr hx))

/-! ### Quasi-preprimitivity via 2-transitivity — the Iwasawa `IsQuasiPreprimitive` obligation

`SL(n,F)` is **2-transitive** on `ℙ^{n-1}(F)` for `2 ≤ |n|`: any ordered pair of distinct
points maps to any other. This is the geometric core; from it, a 2-transitive action is
primitive (`MulAction.isPreprimitive_of_is_two_pretransitive`), and primitive ⇒ quasi-
preprimitive (`IsPreprimitive.isQuasiPreprimitive`, a mathlib instance). The chain runs at
the faithful `PSL = SL/Z` level (the `SL` action itself is *not* quasi-preprimitive — its
center is a nontrivial normal subgroup acting trivially), transported through `QuotientGroup.mk`
exactly as in `SL2.psl_two_trans`/`psl_two_pretrans`/`pslQuasiPreprimitive`.

The single disclosed input is `exists_sl_maps_two_points` (below). -/

omit [DecidableEq n] [Fintype n] in
/-- Two representatives of distinct projective points are linearly independent. -/
theorem rep_pair_li (x0 x1 : Projectivization F (n → F)) (hx : x0 ≠ x1) :
    LinearIndependent F ![x0.rep, x1.rep] := by
  rw [LinearIndependent.pair_iff' (Projectivization.rep_nonzero x0)]
  intro a ha
  apply hx
  have hane : a ≠ 0 := by
    rintro rfl; rw [zero_smul] at ha; exact (Projectivization.rep_nonzero x1) ha.symm
  rw [← Projectivization.mk_rep x0, ← Projectivization.mk_rep x1, Projectivization.mk_eq_mk_iff']
  exact ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ hane, one_smul]⟩

omit [DecidableEq n] in
/-- **Any independent pair maps to any independent pair under a linear automorphism of
`n → F`.** Given linearly independent `(u0,u1)` and `(w0,w1)`, there is a linear
automorphism `T` with `T u0 = w0` and `T u1 = w1`.

Both pairs are extended to bases of `n → F` via `Basis.sumExtend` (which fixes the original
two vectors at the `Sum.inl` indices). The two index sets `Fin 2 ⊕ Su`, `Fin 2 ⊕ Sw` have
equal cardinality (both `= finrank F (n → F) = |n|`), so `Su ≃ Sw`; the sum-equiv fixing the
`Fin 2` part transports one basis onto the other (`Basis.equiv`), giving `T`. -/
theorem exists_linearEquiv_pair (u0 u1 w0 w1 : n → F)
    (hu : LinearIndependent F ![u0, u1]) (hw : LinearIndependent F ![w0, w1]) :
    ∃ T : (n → F) ≃ₗ[F] (n → F), T u0 = w0 ∧ T u1 = w1 := by
  set bu := Basis.sumExtend hu with hbu
  set bw := Basis.sumExtend hw with hbw
  haveI : Fintype (Fin 2 ⊕ (Basis.sumExtendIndex hu)) := FiniteDimensional.fintypeBasisIndex bu
  haveI : Fintype (Fin 2 ⊕ (Basis.sumExtendIndex hw)) := FiniteDimensional.fintypeBasisIndex bw
  haveI : Finite (Basis.sumExtendIndex hu) :=
    Finite.of_injective (Sum.inr : _ → Fin 2 ⊕ _) Sum.inr_injective
  haveI : Finite (Basis.sumExtendIndex hw) :=
    Finite.of_injective (Sum.inr : _ → Fin 2 ⊕ _) Sum.inr_injective
  haveI : Fintype (Basis.sumExtendIndex hu) := Fintype.ofFinite _
  haveI : Fintype (Basis.sumExtendIndex hw) := Fintype.ofFinite _
  have hcu : 2 + Nat.card (Basis.sumExtendIndex hu) = Nat.card n := by
    have h1 := Module.finrank_eq_card_basis bu
    rw [Fintype.card_eq_nat_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_eq_nat_card, Nat.card_sum] at h1
    simpa using h1.symm
  have hcw : 2 + Nat.card (Basis.sumExtendIndex hw) = Nat.card n := by
    have h1 := Module.finrank_eq_card_basis bw
    rw [Fintype.card_eq_nat_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_eq_nat_card, Nat.card_sum] at h1
    simpa using h1.symm
  have hcard' : Fintype.card (Basis.sumExtendIndex hu) = Fintype.card (Basis.sumExtendIndex hw) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]; omega
  set τ : (Basis.sumExtendIndex hu) ≃ (Basis.sumExtendIndex hw) := Fintype.equivOfCardEq hcard'
  set E : (Fin 2 ⊕ Basis.sumExtendIndex hu) ≃ (Fin 2 ⊕ Basis.sumExtendIndex hw) :=
    Equiv.sumCongr (Equiv.refl (Fin 2)) τ
  have huval : ∀ i : Fin 2, bu (Sum.inl i) = ![u0, u1] i := by
    intro i
    simp only [hbu, Basis.sumExtend, Basis.coe_reindex, Function.comp_apply, Equiv.symm_symm]
    rw [Basis.coe_extend]; rfl
  have hwval : ∀ i : Fin 2, bw (Sum.inl i) = ![w0, w1] i := by
    intro i
    simp only [hbw, Basis.sumExtend, Basis.coe_reindex, Function.comp_apply, Equiv.symm_symm]
    rw [Basis.coe_extend]; rfl
  refine ⟨bu.equiv bw E, ?_, ?_⟩
  · have h := bu.equiv_apply (b' := bw) (e := E) (i := Sum.inl 0)
    rw [huval 0] at h
    rw [show (![u0, u1] 0 : n → F) = u0 from rfl] at h
    rw [h]; show bw (E (Sum.inl 0)) = w0
    simp only [E, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]; exact hwval 0
  · have h := bu.equiv_apply (b' := bw) (e := E) (i := Sum.inl 1)
    rw [huval 1] at h
    rw [show (![u0, u1] 1 : n → F) = u1 from rfl] at h
    rw [h]; show bw (E (Sum.inl 1)) = w1
    simp only [E, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]; exact hwval 1

/-- **`SL(n,F)` is 2-transitive on `ℙ^{n-1}(F)`** (for `2 ≤ |n|`; the hypothesis is not
actually needed, since distinctness of the points already forces `|n| ≥ 2`). Any ordered
pair of distinct points `(x₀,x₁)` maps to any other ordered pair of distinct points
`(y₀,y₁)` by some `g : SL(n,F)`.

Proof: distinct points have linearly independent reps (`rep_pair_li`), so by
`exists_linearEquiv_pair` there is a linear automorphism `T` with `T x₀.rep = y₀.rep`,
`T x₁.rep = y₁.rep`. `T` need not have determinant `1`; we correct it by the diagonal
operator `D` (in the basis `bw = sumExtend` adapted to `y₀.rep, y₁.rep`) that scales the
`y₁`-direction by `c = (det T)⁻¹` and fixes everything else. Then `det (D ∘ T) = 1`,
`(D∘T) x₀.rep = y₀.rep` and `(D∘T) x₁.rep = c • y₁.rep ∥ y₁.rep` — so the matrix of `D∘T`
lies in `SL(n,F)` and maps the two lines as required (scaling `y₁.rep` is projectively
invariant). This formerly-axiomatized fact is now fully proved (no reference frame /
`Basis.extend` column bookkeeping needed). -/
theorem exists_sl_maps_two_points (h2 : 2 ≤ Fintype.card n)
    (x0 x1 y0 y1 : Projectivization F (n → F)) (hx : x0 ≠ x1) (hy : y0 ≠ y1) :
    ∃ g : SpecialLinearGroup n F, g • x0 = y0 ∧ g • x1 = y1 := by
  classical
  obtain ⟨T, hT0, hT1⟩ := exists_linearEquiv_pair x0.rep x1.rep y0.rep y1.rep
    (rep_pair_li x0 x1 hx) (rep_pair_li y0 y1 hy)
  set d : F := LinearMap.det (T : (n → F) →ₗ[F] (n → F)) with hd
  have hd_ne : d ≠ 0 := by rw [hd, ← LinearEquiv.coe_det]; exact Units.ne_zero _
  set c : F := d⁻¹ with hc
  have hwLI := rep_pair_li y0 y1 hy
  set bw := Basis.sumExtend hwLI with hbw
  haveI : Fintype (Fin 2 ⊕ (Basis.sumExtendIndex hwLI)) := FiniteDimensional.fintypeBasisIndex bw
  have hwval : ∀ i : Fin 2, bw (Sum.inl i) = ![y0.rep, y1.rep] i := by
    intro i
    simp only [hbw, Basis.sumExtend, Basis.coe_reindex, Function.comp_apply, Equiv.symm_symm]
    rw [Basis.coe_extend]; rfl
  have hw0 : bw (Sum.inl 0) = y0.rep := by simpa using hwval 0
  have hw1 : bw (Sum.inl 1) = y1.rep := by simpa using hwval 1
  set dg : (Fin 2 ⊕ Basis.sumExtendIndex hwLI) → F := fun j => if j = Sum.inl 1 then c else 1
    with hdg
  set D : (n → F) →ₗ[F] (n → F) := Matrix.toLin bw bw (Matrix.diagonal dg) with hD
  have hDval : ∀ j, D (bw j) = dg j • bw j := by
    intro j
    rw [hD, Matrix.toLin_self]
    simp [Matrix.diagonal_apply, Finset.sum_ite_eq']
  have hDdet : LinearMap.det D = c := by
    rw [hD, LinearMap.det_toLin, Matrix.det_diagonal]
    rw [Finset.prod_eq_single (Sum.inl (1 : Fin 2))]
    · simp [hdg]
    · intro b _ hb; simp [hdg, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  set P : (n → F) →ₗ[F] (n → F) := D ∘ₗ (T : (n → F) →ₗ[F] (n → F)) with hP
  have hPdet : LinearMap.det P = 1 := by
    rw [hP, LinearMap.det_comp, hDdet, ← hd, hc, inv_mul_cancel₀ hd_ne]
  have hP0 : P x0.rep = y0.rep := by
    rw [hP, LinearMap.comp_apply, LinearEquiv.coe_coe, hT0, ← hw0, hDval]
    simp [hdg, hw0]
  have hP1 : P x1.rep = c • y1.rep := by
    rw [hP, LinearMap.comp_apply, LinearEquiv.coe_coe, hT1, ← hw1, hDval]
    simp [hdg, hw1]
  have hGdet : (LinearMap.toMatrix' P).det = 1 := by rw [LinearMap.det_toMatrix', hPdet]
  refine ⟨⟨LinearMap.toMatrix' P, hGdet⟩, ?_, ?_⟩
  · conv_lhs => rw [← Projectivization.mk_rep x0]
    rw [Projectivization.smul_mk, ← Projectivization.mk_rep y0, Projectivization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    show (1 : Fˣ) • y0.rep = (LinearMap.toMatrix' P).mulVec x0.rep
    rw [one_smul, LinearMap.toMatrix'_mulVec, hP0]
  · conv_lhs => rw [← Projectivization.mk_rep x1]
    rw [Projectivization.smul_mk, ← Projectivization.mk_rep y1, Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 c (inv_ne_zero hd_ne), ?_⟩
    show (Units.mk0 c (inv_ne_zero hd_ne) : Fˣ) • y1.rep = (LinearMap.toMatrix' P).mulVec x1.rep
    rw [LinearMap.toMatrix'_mulVec, hP1, Units.smul_def, Units.val_mk0]

/-- **`PSL(n,F)` is 2-transitive on `ℙ^{n-1}`** (on points), inherited from the `SL` action
through the surjection `SL ↠ PSL` (modulo the disclosed `exists_sl_maps_two_points`). -/
theorem psln_two_trans [Nonempty n] (h2 : 2 ≤ Fintype.card n)
    (x0 x1 y0 y1 : Projectivization F (n → F)) (hx : x0 ≠ x1) (hy : y0 ≠ y1) :
    letI := pslnAction (n := n) (F := F)
    ∃ g : (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F)),
      g • x0 = y0 ∧ g • x1 = y1 := by
  letI := pslnAction (n := n) (F := F)
  obtain ⟨g, h0, h1⟩ := exists_sl_maps_two_points h2 x0 x1 y0 y1 hx hy
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · show pslnPermHom (QuotientGroup.mk g) x0 = y0
    rw [pslnPermHom_mk]; exact h0
  · show pslnPermHom (QuotientGroup.mk g) x1 = y1
    rw [pslnPermHom_mk]; exact h1

/-- **`PSL(n,F)` is 2-pretransitive on `ℙ^{n-1}`** (the mathlib `IsMultiplyPretransitive`
form, on ordered pairs `Fin 2 ↪ ℙ^{n-1}`). -/
theorem psln_two_pretransitive [Nonempty n] (h2 : 2 ≤ Fintype.card n) :
    letI := pslnAction (n := n) (F := F)
    MulAction.IsMultiplyPretransitive
      (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) 2 := by
  letI := pslnAction (n := n) (F := F)
  rw [MulAction.isMultiplyPretransitive_iff]
  intro x y
  have hx : x 0 ≠ x 1 := fun h => absurd (x.injective h) (by decide)
  have hy : y 0 ≠ y 1 := fun h => absurd (y.injective h) (by decide)
  obtain ⟨g, hg0, hg1⟩ := psln_two_trans h2 (x 0) (x 1) (y 0) (y 1) hx hy
  refine ⟨g, ?_⟩
  ext i
  fin_cases i
  · simpa [Function.Embedding.smul_apply] using hg0
  · simpa [Function.Embedding.smul_apply] using hg1

/-- **`PSL(n,F)`'s action on `ℙ^{n-1}` is quasi-preprimitive** for `2 ≤ |n|` — the Iwasawa
`IsQuasiPreprimitive` obligation. From 2-transitivity: 2-transitive ⇒ primitive
(`isPreprimitive_of_is_two_pretransitive`) ⇒ quasi-preprimitive (mathlib instance). Modulo
the disclosed `exists_sl_maps_two_points`. Generalizes `SL2.pslQuasiPreprimitive`. -/
@[reducible]
noncomputable def pslnQuasiPreprimitive [Nonempty n] (h2 : 2 ≤ Fintype.card n) :
    letI := pslnAction (n := n) (F := F)
    MulAction.IsQuasiPreprimitive
      (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) := by
  letI := pslnAction (n := n) (F := F)
  haveI : MulAction.IsPreprimitive
      (SpecialLinearGroup n F ⧸ Subgroup.center (SpecialLinearGroup n F))
      (Projectivization F (n → F)) :=
    MulAction.isPreprimitive_of_is_two_pretransitive (psln_two_pretransitive h2)
  infer_instance

end FiniteSimpleGroups.SLn

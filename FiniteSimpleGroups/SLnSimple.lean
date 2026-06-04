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

open Matrix

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

/-- **`SL(n,F)` is 2-transitive on `ℙ^{n-1}` for `2 ≤ |n|`** — DISCLOSED AXIOM (out at
Aristotle / TODO). Any ordered pair of distinct points `(x₀,x₁)` maps to any other ordered
pair of distinct points `(y₀,y₁)` by some `g : SL(n,F)`.

Mathematical content: distinct projective points have linearly independent representatives.
Given distinct `x₀,x₁` with reps `u,v` (l.i.) and distinct `y₀,y₁` with reps `u',v'` (l.i.),
extend `{u,v}` and `{u',v'}` to bases; the matrices `A,B` with these as their first two
columns are invertible, and rescaling the *second* column by `1/det` makes `det = 1` without
moving the line it spans (projective invariance), giving `A,B ∈ SL(n,F)` mapping the
reference frame `([e₀],[e₁])` to `(x₀,x₁)` and `(y₀,y₁)`; then `B A⁻¹` is the required element.
The `2 ≤ |n|` hypothesis guarantees two distinct standard basis lines exist. For `n = 2` this
is `SL2.sl2_two_trans` (proved); the general case needs mathlib's `Basis.extend` plus the
column-to-matrix/determinant bookkeeping (a self-contained linear-algebra brick).

TODO(discharge): port the Aristotle proof (or prove locally via `Basis.extend`). Once landed,
`pslnQuasiPreprimitive` becomes axiom-clean. -/
axiom exists_sl_maps_two_points (h2 : 2 ≤ Fintype.card n)
    (x0 x1 y0 y1 : Projectivization F (n → F)) (hx : x0 ≠ x1) (hy : y0 ≠ y1) :
    ∃ g : SpecialLinearGroup n F, g • x0 = y0 ∧ g • x1 = y1

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

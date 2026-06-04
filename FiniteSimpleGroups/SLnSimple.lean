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

end FiniteSimpleGroups.SLn

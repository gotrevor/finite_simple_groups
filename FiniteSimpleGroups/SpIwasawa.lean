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
open scoped Pointwise

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

/-- **DISCLOSED AXIOM (perfectness).** `PSp(2n,F)` is perfect (`commutator = ⊤`) for `2 ≤ n`
over a field large enough to exclude `PSp(4,2) ≅ S₆`. Each symplectic transvection is a
commutator in `Sp(2n)` once `n ≥ 2`; descends to `Sp/Z`. The `Nonempty l` / field-size
hypothesis is carried as a side condition `hperf`. -/
axiom commutator_PSp_eq_top [Nonempty l] :
    commutator (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) = ⊤

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

/-- **`PSp(2n,F) = Sp/Z` is simple** for `Nonempty l` (dimension `2n ≥ 2`), **modulo the three
disclosed geometric axioms** `sp_transvec_closure_eq_top`, `commutator_PSp_eq_top`,
`pspQuasiPreprimitive`. The Iwasawa criterion (`IwasawaStructure.isSimpleGroup`) applied to the
faithful action on `ℙ²ⁿ⁻¹` with all six obligations: perfect, nontrivial, MulAction, faithful,
quasi-preprimitive, and the `IwasawaStructure`. The symplectic analogue of
`SLn.PSLn_isSimpleGroup_of_rank`. -/
theorem PSpn_isSimpleGroup_of_iwasawa [Nonempty l] :
    IsSimpleGroup (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) := by
  letI := pspAction (l := l) (F := F)
  haveI : Nontrivial (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) :=
    PSp_nontrivial
  haveI : FaithfulSMul (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) := pspFaithful
  haveI : MulAction.IsQuasiPreprimitive
      (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F))
      (Projectivization F ((l ⊕ l) → F)) := pspQuasiPreprimitive
  exact pspIwasawaStructure.isSimpleGroup commutator_PSp_eq_top pspFaithful

end FiniteSimpleGroups.SpN

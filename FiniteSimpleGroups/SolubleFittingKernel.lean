import FiniteSimpleGroups.FittingSubgroup

/-!
# The soluble Fitting self-centralizing kernel

This file proves the **soluble base case of Bender's cornerstone**:

> A finite **solvable** group `G` whose Fitting subgroup is central
> (`F(G) ≤ Z(G)`) satisfies `F(G) = ⊤` (equivalently, `G` is nilpotent — in fact
> abelian, since `F(G) ≤ Z(G) ≤ F(G)`).

This is the soluble-type self-centralizing fact `C_G(F(G)) ≤ F(G)` (Fitting's
theorem / Hall) in its purest central form. (Aschbacher, *Finite Group Theory*
31.13; Kurzweil–Stellmacher 6.5.8.)

## History / soundness note

The `[IsSolvable G]` hypothesis is **essential**. Without it the statement is
*false*: `SL(2, 𝔽₅)` (order 120) is a counterexample — its only minimal normal
subgroup is the central `ℤ/2`, and `F(G) = Z(G) = ℤ/2`, so `F(G) ≤ Z(G)` holds,
yet `F(G) ≠ ⊤`. An earlier formalization in this repo replaced solvability by the
strictly weaker "every minimal normal subgroup is abelian" and was therefore
unsound; `SL(2, 𝔽₅)` satisfies that hypothesis too. The counterexample and the
proof below were found by Aristotle (Harmonic's auto-formalizer) on 2026-06-02,
then ported and re-checked in this repo's kernel.

The proof is a contradiction argument: if `F(G) ≠ ⊤` then `G/Z(G)` is a nontrivial
finite solvable group, hence has a nontrivial abelian normal subgroup `A`; its
preimage `N` in `G` has `Z(G) ≤ N`, `N/Z(G)` abelian, and `Z(G) ≤ Z(N)`, so `N` is
nilpotent. Being normal and nilpotent, `N ≤ F(G) = Z(G)`, contradicting `Z(G) < N`.

## Remaining gap to discharge `fittingSubgroup_eq_top_of_layer_eq_bot_of_le_center`

The Bender kernel needs the *layer = ⊥* form, not the *solvable* form. The residual
gap is `layer G = ⊥ → IsSolvable G` (under `F(G) ≤ Z(G)`); see
`GeneralizedFitting.lean`. This theorem supplies the engine for that discharge.
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

/-- If `G` is nilpotent then `F(G) = ⊤` (`G` itself is normal and nilpotent). -/
theorem fittingSubgroup_eq_top_of_isNilpotent (G : Type*) [Group G]
    [Group.IsNilpotent G] : fittingSubgroup G = ⊤ :=
  le_antisymm le_top (le_sSup ⟨inferInstance, inferInstance⟩)

/-- A nontrivial finite solvable group has a nontrivial **abelian** normal subgroup
— the last nontrivial term of the derived series. -/
theorem exists_nontrivial_abelian_normal_of_solvable (G : Type*) [Group G]
    [Finite G] [IsSolvable G] [Nontrivial G] :
    ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧
      ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  obtain ⟨n, hn⟩ : ∃ n, derivedSeries G n ≠ ⊥ ∧ derivedSeries G (n + 1) = ⊥ := by
    obtain ⟨n, hn⟩ := ‹IsSolvable G›
    contrapose! hn
    induction' n with n ih <;> simp_all +decide [derivedSeries]
  refine ⟨derivedSeries G n, ?_, hn.1, ?_⟩ <;>
    simp_all +decide [Subgroup.commutator_eq_bot_iff_le_centralizer]
  · exact derivedSeries_normal G n
  · exact fun a ha b hb => by have := hn.2 ha b hb; simp_all +decide

/-- If `N ≤ Z(G)` is central with `G ⧸ N` nilpotent, then `G` is nilpotent. -/
theorem isNilpotent_of_quotient_by_central_isNilpotent (G : Type*) [Group G]
    (N : Subgroup G) [N.Normal] (hc : N ≤ Subgroup.center G)
    (hq : Group.IsNilpotent (G ⧸ N)) : Group.IsNilpotent G := by
  convert of_quotient_center_nilpotent _
  -- `N ≤ Z(G)` gives a surjection `G/N ↠ G/Z(G)`, transporting nilpotency.
  have h_surj : ∃ f : G ⧸ N →* G ⧸ Subgroup.center G, Function.Surjective f := by
    refine ⟨QuotientGroup.lift N (QuotientGroup.mk' (Subgroup.center G)) ?_, ?_⟩
    · simp +decide [hc, QuotientGroup.ker_mk']
    · exact fun x => by
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
        exact ⟨QuotientGroup.mk y, rfl⟩
  exact nilpotent_of_surjective _ h_surj.choose_spec

/-- **`F(G/Z(G)) = ⊥` when `F(G) ≤ Z(G)`.** If the Fitting subgroup is central then the
Fitting subgroup of `G/Z(G)` is trivial. A nilpotent normal subgroup `A` of `G/Z(G)`
pulls back to a normal subgroup `N` of `G` with `Z(G) ≤ N` and `N/(Z(G) ⊓ N) ≅ A`
nilpotent; since `Z(G) ⊓ N ≤ Z(N)`, `N` is nilpotent, so `N ≤ F(G) ≤ Z(G)`, forcing
`A = ⊥`. This is the fact that defeats the naïve "the central quotient inherits
`F ≤ Z`" worry in the solvability induction: the quotient's Fitting subgroup is not
just central, it is *trivial*. -/
theorem fittingSubgroup_quotient_center_eq_bot (G : Type*) [Group G] [Finite G]
    (hF : fittingSubgroup G ≤ Subgroup.center G) :
    fittingSubgroup (G ⧸ Subgroup.center G) = ⊥ := by
  -- It suffices to show every nilpotent normal subgroup `A` of `G/Z(G)` is trivial.
  suffices key : ∀ A : Subgroup (G ⧸ Subgroup.center G), A.Normal →
      Group.IsNilpotent A → A = ⊥ by
    exact key _ (fittingSubgroup_normal _) (fittingSubgroup_isNilpotent _)
  intro A hAnorm hAnil
  set Z := Subgroup.center G with hZ
  haveI hZN : Z.Normal := by rw [hZ]; infer_instance
  set π := QuotientGroup.mk' Z with hπ
  set N := A.comap π with hNdef
  haveI hNnorm : N.Normal := hAnorm.comap π
  -- `φ : ↥N →* G/Z`, with `range φ = A` and `ker φ = Z.subgroupOf N`.
  set φ := π.comp N.subtype with hφ
  have hker : φ.ker = Z.subgroupOf N := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hrange : φ.range = A := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hNdef,
      Subgroup.map_comap_eq, hπ, QuotientGroup.range_mk', top_inf_eq]
  -- `N/(Z ⊓ N) ≅ A` is nilpotent, hence so is `N/(Z.subgroupOf N)`.
  haveI hAnil' : Group.IsNilpotent φ.range := hrange ▸ hAnil
  haveI hqnil : Group.IsNilpotent (N ⧸ Z.subgroupOf N) := by
    haveI hnil : Group.IsNilpotent (N ⧸ φ.ker) :=
      nilpotent_of_mulEquiv (QuotientGroup.quotientKerEquivRange φ).symm
    exact nilpotent_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hker)
  -- `Z ⊓ N` is central in `N`, so `N` is nilpotent (central-by-nilpotent).
  have hcentral : Z.subgroupOf N ≤ Subgroup.center N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro n
    exact Subtype.ext (by simpa using Subgroup.mem_center_iff.mp hx (n : G))
  haveI hNnil : Group.IsNilpotent N :=
    isNilpotent_of_quotient_by_central_isNilpotent N (Z.subgroupOf N) hcentral hqnil
  -- `N` normal and nilpotent ⟹ `N ≤ F(G) ≤ Z`; then `A = map π N ≤ map π Z = ⊥`.
  have hNleZ : N ≤ Z :=
    (normal_nilpotent_le_fittingSubgroup N hNnorm hNnil).trans hF
  have hAmap : A = N.map π := by
    rw [hNdef, Subgroup.map_comap_eq, hπ, QuotientGroup.range_mk']; simp
  rw [hAmap]
  refine le_antisymm ?_ bot_le
  calc N.map π ≤ Z.map π := Subgroup.map_mono hNleZ
    _ = ⊥ := by
        rw [hπ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

/-- **The soluble Fitting kernel (Bender's soluble base case).** A finite *solvable*
group whose Fitting subgroup is central has `F(G) = ⊤`.

Proof (ported from Aristotle, re-checked in-kernel): contradiction via a nontrivial
abelian normal subgroup of `G/Z(G)`. -/
theorem fittingSubgroup_eq_top_of_isSolvable_of_le_center (G : Type*) [Group G]
    [Finite G] [IsSolvable G] (hF : fittingSubgroup G ≤ Subgroup.center G) :
    fittingSubgroup G = ⊤ := by
  by_contra! h_contra
  -- `G/Z(G)` is a nontrivial finite solvable group: extract an abelian normal `A`.
  obtain ⟨A, hA_normal, hA_nontrivial, hA_abelian⟩ :
      ∃ A : Subgroup (G ⧸ Subgroup.center G), A.Normal ∧ A ≠ ⊥ ∧
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) := by
    convert exists_nontrivial_abelian_normal_of_solvable (G ⧸ Subgroup.center G)
    contrapose! h_contra
    exact le_top.antisymm (le_trans (by aesop) center_le_fittingSubgroup)
  -- The preimage `N` of `A` in `G`: normal, contains `Z(G)`, with `N/Z(G)` nilpotent.
  obtain ⟨N, hN_normal, hN_center, hN_quotient⟩ :
      ∃ N : Subgroup G, N.Normal ∧ Subgroup.center G ≤ N ∧
        N.map (QuotientGroup.mk' (Subgroup.center G)) = A ∧
        Group.IsNilpotent (N ⧸ (Subgroup.center G).subgroupOf N) := by
    refine ⟨Subgroup.comap (QuotientGroup.mk' (Subgroup.center G)) A, ?_, ?_, ?_, ?_⟩ <;>
      simp_all +decide [Subgroup.normal_comap]
    · intro x hx; simp +decide
      convert A.one_mem using 1; aesop
    · rw [Subgroup.map_comap_eq_self]; aesop_cat
    · -- `A` abelian ⟹ `N/Z(G)` abelian ⟹ nilpotent.
      have hN_quotient_abelian :
          ∀ a b : ↥(Subgroup.comap (QuotientGroup.mk' (Subgroup.center G)) A) ⧸
              (Subgroup.center G).subgroupOf
                (Subgroup.comap (QuotientGroup.mk' (Subgroup.center G)) A),
            a * b = b * a := by
        rintro ⟨a⟩ ⟨b⟩
        erw [QuotientGroup.eq]
        simp +decide [Subgroup.mem_subgroupOf]
        have := hA_abelian (QuotientGroup.mk' (Subgroup.center G) a) a.2
          (QuotientGroup.mk' (Subgroup.center G) b) b.2
        simp_all +decide [← mul_assoc]
        erw [QuotientGroup.eq] at this
        simp_all +decide [mul_assoc, Subgroup.mem_center_iff]
      refine ⟨1, ?_⟩
      simp +decide [Subgroup.eq_top_iff']
      simp +decide [Subgroup.mem_center_iff, hN_quotient_abelian]
  -- `Z(G) ≤ Z(N)` and `N/Z(G)` nilpotent ⟹ `N` nilpotent.
  have hN_nilpotent : Group.IsNilpotent N := by
    convert isNilpotent_of_quotient_by_central_isNilpotent N
      ((Subgroup.center G).subgroupOf N) ?_ ?_
    · intro x hx
      simp_all +decide [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
      exact fun g hg => Subtype.ext (hx g)
    · exact hN_quotient.2
  -- `N` normal + nilpotent ⟹ `N ≤ F(G) = Z(G)`, contradicting `Z(G) < N`.
  have hN_le_center : N ≤ Subgroup.center G :=
    le_trans (normal_nilpotent_le_fittingSubgroup N hN_normal hN_nilpotent) hF
  simp_all +decide [le_antisymm hN_le_center hN_center]

end FiniteSimpleGroups

import Mathlib

/-!
# Character theory toward Burnside's `p^a q^b` theorem

This file develops the character-theoretic bricks needed to discharge the sharp axiom
`isSimpleGroup_centralizer_index_not_primePow` of `FiniteSimpleGroups.Burnside` (Burnside's
prime-power class-size lemma).  The classical proof of that lemma needs six ingredients:

1. **`χ(g)` is an algebraic integer.**  ✅ proved here (`trace_isIntegral_of_pow_eq_one`,
   `Representation.character_isIntegral`): for a finite group the matrix of `ρ g` has finite
   order, its eigenvalues are roots of unity (integral over `ℤ`), and the trace is their sum.
2. **Central-character integrality** `[G:C_G(g)]·χ(g)/χ(1)` is an algebraic integer.  ⛔ needs
   the class-sum / centre-of-group-algebra machinery, **not in mathlib v4.29.1** — the main gap.
3. **Column orthogonality** `∑_χ χ(1) χ(g) = 0` for `g ≠ 1`.  ⛔ mathlib has only row
   orthonormality (`char_orthonormal`); column orthogonality is the second gap.
4. **Kronecker's theorem** — an algebraic integer all of whose conjugates lie in the closed unit
   disc is `0` or a root of unity.  ✅ already in mathlib
   (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`).
5. **`-1/p` is not an algebraic integer.**  ✅ easy (`ℤ` integrally closed in `ℚ`); recorded here
   as `not_isIntegral_neg_inv_prime`.
6. **Scalar ⟹ proper normal subgroup**, contradicting simplicity.  Group/representation theory.

So after this file the only genuinely missing mathlib infrastructure is (2) and (3).
-/

namespace FiniteSimpleGroups

open Matrix Polynomial

/-- **The trace of a finite-order complex matrix is an algebraic integer.**
If `M : Matrix (Fin d) (Fin d) ℂ` satisfies `M ^ n = 1` with `n ≥ 1`, then `Matrix.trace M`
is integral over `ℤ`.

Proof: `M` satisfies the separable polynomial `X ^ n - 1` over `ℂ`, so its characteristic
polynomial splits with roots in the spectrum of `M`; each spectral value `r` satisfies
`r ^ n = 1` (spectral mapping: `r ^ n ∈ spectrum (M ^ n) = spectrum 1 = {1}`), hence is integral
over `ℤ` (a root of the monic integer polynomial `X ^ n - 1`).  The trace is the sum of these
roots, and a finite sum of algebraic integers is an algebraic integer. -/
theorem trace_isIntegral_of_pow_eq_one
    {d n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : M ^ n = 1) : IsIntegral ℤ (Matrix.trace M) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_empty]
    exact isIntegral_zero
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    haveI : Nontrivial (Matrix (Fin d) (Fin d) ℂ) := inferInstance
    -- the spectrum of `1` is `{1}`
    have hone : ∀ x : ℂ, x ∈ spectrum ℂ (1 : Matrix (Fin d) (Fin d) ℂ) → x = 1 := by
      intro x hx
      rw [spectrum.mem_iff] at hx
      by_contra hxne
      apply hx
      have he : algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) x - 1
          = algebraMap ℂ _ (x - 1) := by rw [map_sub, map_one]
      rw [he]
      exact (algebraMap ℂ _).isUnit_map (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxne))
    -- each root of the characteristic polynomial is an `n`-th root of unity, hence integral
    have hroot : ∀ r ∈ (Matrix.charpoly M).roots, IsIntegral ℤ r := by
      intro r hr
      have hr_spec : r ∈ spectrum ℂ M := by
        rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
        exact (Polynomial.mem_roots (M.charpoly_monic.ne_zero)).mp hr
      have hmap := spectrum.subset_polynomial_aeval M ((X : ℂ[X]) ^ n)
      have hin : eval r ((X : ℂ[X]) ^ n) ∈ spectrum ℂ (aeval M ((X : ℂ[X]) ^ n)) :=
        hmap ⟨r, hr_spec, rfl⟩
      rw [map_pow, aeval_X, hM, eval_pow, eval_X] at hin
      have hrn : r ^ n = 1 := hone _ hin
      refine ⟨X ^ n - C 1, ?_, ?_⟩
      · exact monic_X_pow_sub_C 1 (by omega)
      · rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_one, hrn, sub_self]
    rw [Matrix.trace_eq_sum_roots_charpoly]
    exact (integralClosure ℤ ℂ).multiset_sum_mem hroot

/-- **Character values of a finite group are algebraic integers.**
For a finite group `G` and a finite-dimensional complex representation `ρ`, every character
value `ρ.character g` is integral over `ℤ`. -/
theorem Representation.character_isIntegral {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) : IsIntegral ℤ (ρ.character g) := by
  classical
  let b := Module.finBasis ℂ V
  show IsIntegral ℤ (LinearMap.trace ℂ V (ρ g))
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  refine trace_isIntegral_of_pow_eq_one (orderOf_pos g) _ ?_
  rw [LinearMap.toMatrix_pow, ← map_pow, pow_orderOf_eq_one, map_one, LinearMap.toMatrix_one]

end FiniteSimpleGroups

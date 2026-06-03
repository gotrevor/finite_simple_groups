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
6. **Scalar ⟹ proper normal subgroup**, contradicting simplicity.  ✅ structural half proved here
   (`scalarSubgroup`, `scalarSubgroup_normal`, `comm_of_scalarSubgroup_eq_top`).

So after this file the only genuinely missing mathlib infrastructure is (2) and (3) — the
central-character / class-sum integrality and column orthogonality.  Ingredients 1, 4, 5, 6 are
in hand (in-repo or mathlib).
-/

namespace FiniteSimpleGroups

open Matrix Polynomial

/-- **Eigenvalue structure of a finite-order complex matrix.**  If `M ^ n = 1`, the roots of the
characteristic polynomial of `M` (its eigenvalues, with multiplicity) form a multiset of size
exactly `d` (`= dim`), each of which is an `n`-th root of unity.

Via the spectral mapping theorem: a root `r` of `charpoly M` lies in `spectrum ℂ M`, so
`r ^ n = eval r (X^n) ∈ spectrum ℂ (M ^ n) = spectrum ℂ 1 = {1}`.  The card is `d` because over
the algebraically closed field `ℂ` the (monic, degree-`d`) characteristic polynomial splits. -/
theorem charpoly_roots_pow_eq_one {d n : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : M ^ n = 1) :
    (Matrix.charpoly M).roots.card = d ∧ ∀ r ∈ (Matrix.charpoly M).roots, r ^ n = 1 := by
  refine ⟨?_, ?_⟩
  · rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
        Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · intro r hr
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp [Matrix.charpoly] at hr
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
      have hr_spec : r ∈ spectrum ℂ M := by
        rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
        exact (Polynomial.mem_roots (M.charpoly_monic.ne_zero)).mp hr
      have hmap := spectrum.subset_polynomial_aeval M ((X : ℂ[X]) ^ n)
      have hin : eval r ((X : ℂ[X]) ^ n) ∈ spectrum ℂ (aeval M ((X : ℂ[X]) ^ n)) :=
        hmap ⟨r, hr_spec, rfl⟩
      rw [map_pow, aeval_X, hM, eval_pow, eval_X] at hin
      exact hone _ hin

/-- **The trace of a finite-order complex matrix is an algebraic integer.**
If `M : Matrix (Fin d) (Fin d) ℂ` satisfies `M ^ n = 1` with `n ≥ 1`, then `Matrix.trace M`
is integral over `ℤ`: the trace is the sum of the eigenvalues
(`charpoly_roots_pow_eq_one`), each an `n`-th root of unity, hence a root of the monic integer
polynomial `X ^ n - 1`; a finite sum of algebraic integers is an algebraic integer. -/
theorem trace_isIntegral_of_pow_eq_one
    {d n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : M ^ n = 1) : IsIntegral ℤ (Matrix.trace M) := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine (integralClosure ℤ ℂ).multiset_sum_mem (fun r hr => ?_)
  have hrn : r ^ n = 1 := (charpoly_roots_pow_eq_one M hM).2 r hr
  refine ⟨X ^ n - C 1, monic_X_pow_sub_C 1 (by omega), ?_⟩
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_one, hrn, sub_self]

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

/-- **`‖trace M‖ ≤ d`** for a finite-order `d × d` complex matrix (`M ^ n = 1`, `n ≥ 1`): the
trace is a sum of `d` eigenvalues, each of modulus `1` (a root of unity). -/
theorem norm_trace_le_of_pow_eq_one {d n : ℕ} (hn : 1 ≤ n) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : M ^ n = 1) : ‖Matrix.trace M‖ ≤ (d : ℝ) := by
  obtain ⟨hcard, hpow⟩ := charpoly_roots_pow_eq_one M hM
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine (norm_multiset_sum_le _).trans ?_
  refine (Multiset.sum_le_card_nsmul _ 1 ?_).trans ?_
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    have hrn : ‖r‖ ^ n = 1 := by rw [← norm_pow, hpow r hr, norm_one]
    by_contra hgt
    rw [not_le] at hgt
    have h1 : 1 < ‖r‖ ^ n := one_lt_pow₀ hgt (by omega)
    rw [hrn] at h1
    exact lt_irrefl 1 h1
  · rw [Multiset.card_map, hcard, nsmul_eq_mul, mul_one]

/-- **`‖χ(g)‖ ≤ χ(1)`**: a character value of a finite group is bounded in modulus by the
degree `χ(1) = Module.finrank ℂ V` (the eigenvalues of `ρ g` are roots of unity, so their sum has
modulus `≤ dim`).  This is the bound that makes `χ(g)/χ(1)` lie in the closed unit disc, feeding
Kronecker's theorem in Burnside's vanishing lemma. -/
theorem Representation.norm_character_le {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ‖ρ.character g‖ ≤ (Module.finrank ℂ V : ℝ) := by
  classical
  let b := Module.finBasis ℂ V
  show ‖LinearMap.trace ℂ V (ρ g)‖ ≤ _
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  refine norm_trace_le_of_pow_eq_one (orderOf_pos g) _ ?_
  rw [LinearMap.toMatrix_pow, ← map_pow, pow_orderOf_eq_one, map_one, LinearMap.toMatrix_one]

/-- **`-1/p` is not an algebraic integer** for a prime `p` (ingredient 5/6).  A rational that is
integral over `ℤ` is an integer (`ℤ` is integrally closed in `ℚ`), and `-1/p ∉ ℤ` for `p ≥ 2`.
This is what — against the column-orthogonality relation `1 + ∑_{χ≠1} χ(1)χ(g)/p = 0` rewritten
as `-1/p = ∑_{χ≠1} (χ(1)/p)χ(g)` — forces some nontrivial irreducible `χ` with `p ∤ χ(1)` and
`χ(g) ≠ 0`. -/
theorem not_isIntegral_neg_inv_prime {p : ℕ} (hp : p.Prime) :
    ¬ IsIntegral ℤ (-(p : ℚ)⁻¹) := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  rintro ⟨m, hm⟩
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hm' : (m : ℚ) = -(p : ℚ)⁻¹ := by exact_mod_cast hm
  have hmp : (m : ℚ) * p = -1 := by rw [hm', neg_mul, inv_mul_cancel₀ hp0]
  have hmZ : m * (p : ℤ) = -1 := by exact_mod_cast hmp
  have hdvd : (p : ℤ) ∣ -1 := ⟨m, by rw [mul_comm]; exact hmZ.symm⟩
  have hp1 : (p : ℤ) ∣ 1 := (Int.dvd_neg).mp hdvd
  have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hp1
  have h2 : 2 ≤ p := hp.two_le
  omega

/-! ### Ingredient 6/6: scalar elements form a normal subgroup

In an irreducible representation of a simple group, the elements acting as a scalar form a
proper nontrivial normal subgroup once some nontrivial element does — contradicting simplicity.
These lemmas supply the structural half of that argument (independent of the missing class-sum /
orthogonality machinery). -/

section ScalarSubgroup

variable {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The set of group elements acting as a scalar `c • 1 = algebraMap ℂ (End ℂ V) c` in a
representation `ρ`, as a subgroup of `G`.  `inv_mem` uses that `g⁻¹ = g ^ (orderOf g - 1)` in a
finite group, so a scalar's inverse is a (power of a) scalar — avoiding any nonvanishing argument. -/
def scalarSubgroup (ρ : Representation ℂ G V) : Subgroup G where
  carrier := {g | ∃ c : ℂ, ρ g = algebraMap ℂ (Module.End ℂ V) c}
  one_mem' := ⟨1, by rw [map_one, map_one]⟩
  mul_mem' := by
    rintro a b ⟨ca, ha⟩ ⟨cb, hb⟩
    exact ⟨ca * cb, by rw [map_mul, ha, hb, map_mul]⟩
  inv_mem' := by
    rintro a ⟨c, ha⟩
    have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
      have h1 : a * a ^ (orderOf a - 1) = a ^ orderOf a := by
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a)]
      rw [pow_orderOf_eq_one] at h1
      exact inv_eq_of_mul_eq_one_right h1
    exact ⟨c ^ (orderOf a - 1), by rw [hinv, map_pow, ha, ← map_pow]⟩

/-- The scalar subgroup is normal: a conjugate `ρ(h g h⁻¹) = ρh · (c•1) · ρh⁻¹ = c•1` is still a
scalar (scalars are central in the endomorphism algebra). -/
theorem scalarSubgroup_normal (ρ : Representation ℂ G V) : (scalarSubgroup ρ).Normal := by
  constructor
  rintro a ⟨c, ha⟩ h
  refine ⟨c, ?_⟩
  rw [map_mul, map_mul, ha, ← Algebra.commutes c (ρ h), mul_assoc, ← map_mul,
    mul_inv_cancel, map_one, mul_one]

/-- If every element acts as a scalar (`scalarSubgroup ρ = ⊤`), the image of `ρ` is abelian; for
a faithful `ρ` this makes `G` itself abelian.  This is the contradiction in Burnside's argument:
a nonabelian simple group with a faithful irreducible `ρ` cannot have `scalarSubgroup ρ = ⊤`, yet
a nontrivial scalar element forces `scalarSubgroup ρ ≠ ⊥`, so by simplicity it would be `⊤`. -/
theorem comm_of_scalarSubgroup_eq_top (ρ : Representation ℂ G V)
    (htop : scalarSubgroup ρ = ⊤) (hinj : Function.Injective ρ) (a b : G) :
    a * b = b * a := by
  apply hinj
  obtain ⟨ca, hca⟩ : a ∈ scalarSubgroup ρ := by rw [htop]; exact Subgroup.mem_top a
  obtain ⟨cb, hcb⟩ : b ∈ scalarSubgroup ρ := by rw [htop]; exact Subgroup.mem_top b
  rw [map_mul, map_mul, hca, hcb, ← map_mul, ← map_mul, mul_comm]

end ScalarSubgroup

end FiniteSimpleGroups

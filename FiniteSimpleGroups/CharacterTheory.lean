import Mathlib

/-!
# Character theory toward Burnside's `p^a q^b` theorem

This file develops the character-theoretic bricks needed to discharge the sharp axiom
`isSimpleGroup_centralizer_index_not_primePow` of `FiniteSimpleGroups.Burnside` (Burnside's
prime-power class-size lemma).  The classical proof of that lemma needs six ingredients:

1. **`χ(g)` is an algebraic integer.**  ✅ proved here (`trace_isIntegral_of_pow_eq_one`,
   `Representation.character_isIntegral`): for a finite group the matrix of `ρ g` has finite
   order, its eigenvalues are roots of unity (integral over `ℤ`), and the trace is their sum.
2. **Central-character integrality** `[G:C_G(g)]·χ(g)/χ(1)` is an algebraic integer.  ✅ proved
   here (`classSize_char_isIntegral`) via class sums in `ℂ[G]` and Schur's lemma — the textbook
   structure-constant argument is bypassed because `ℤ[G]` is module-finite over `ℤ`, so every class
   sum is integral for free.
3. **Column orthogonality** `∑_χ χ(1) χ(g) = 0` for `g ≠ 1`.  ⛔ mathlib has only row
   orthonormality (`char_orthonormal`); column orthogonality is the one remaining gap.
4. **Kronecker's theorem** — an algebraic integer all of whose conjugates lie in the closed unit
   disc is `0` or a root of unity.  ✅ already in mathlib
   (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`).
5. **`-1/p` is not an algebraic integer.**  ✅ easy (`ℤ` integrally closed in `ℚ`); recorded here
   as `not_isIntegral_neg_inv_prime`.
6. **Scalar ⟹ proper normal subgroup**, contradicting simplicity.  ✅ structural half proved here
   (`scalarSubgroup`, `scalarSubgroup_normal`, `comm_of_scalarSubgroup_eq_top`).

So after this file the only genuinely missing mathlib infrastructure is (3) — column
orthogonality.  Ingredients 1, 2, 4, 5, 6 are in hand (in-repo or mathlib).
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

/-! ### Ingredient 2/6: central-character integrality (class sums)

This section discharges ingredient 2: for a finite group, an irreducible complex representation
`ρ` with character `χ`, and `g : G`, the number `(class size of g)·χ(g)/χ(1)` is an algebraic
integer.  The classical proof goes through class sums in the group algebra and Schur's lemma.

The key simplification (versus the textbook structure-constant argument) is that **every** element
of `ℤ[G]` is integral over `ℤ`, because `ℤ[G]` is module-finite over `ℤ` (free of rank `|G|`).  So
the class sum is integral for free; centrality of the class sum is needed only to make `ρ` send it
to a scalar (Schur), not for integrality. -/

section CentralCharacter

open Representation
open scoped MonoidAlgebra Classical

variable {G : Type*} [Group G]

/-- **Abstract central-character lemma.** If `z : ℂ[G]` acts (via an irreducible `ρ`) commuting
with the whole `G`-action and is integral over `ℤ`, then `ρ` sends it to a scalar `c • 1` with `c`
an algebraic integer.  (Schur's lemma: a `G`-equivariant endomorphism of an irreducible complex
representation is a scalar; integrality transfers along the algebra map `ℂ[G] → End ℂ V` and is
reflected back to `ℂ` since `ℂ → End ℂ V` is injective.) -/
theorem exists_scalar_isIntegral_of_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (z : MonoidAlgebra ℂ G)
    (hzc : ∀ g v, (ρ.asAlgebraHom z) (ρ g v) = ρ g ((ρ.asAlgebraHom z) v))
    (hzi : IsIntegral ℤ z) :
    ∃ c : ℂ, ρ.asAlgebraHom z = algebraMap ℂ (Module.End ℂ V) c ∧ IsIntegral ℤ c := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ρ.asAlgebraHom z = algebraMap ℂ (Module.End ℂ V) c := by
    let f : Representation.IntertwiningMap ρ ρ :=
      LinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ (ρ.asAlgebraHom z) hzc
    obtain ⟨c, hcf⟩ :=
      (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
        (ρ := ρ)).2 f
    refine ⟨c, ?_⟩
    have : (algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c).toLinearMap = f.toLinearMap := by
      rw [hcf]
    rw [Representation.IntertwiningMap.algebraMap_apply] at this
    ext v
    have h2 := LinearMap.congr_fun this v
    simpa [f, LinearMap.intertwiningMap_of_isIntertwiningMap,
      Algebra.algebraMap_eq_smul_one] using h2.symm
  refine ⟨c, hc, ?_⟩
  have h1 : IsIntegral ℤ (ρ.asAlgebraHom z) := hzi.map (ρ.asAlgebraHom.restrictScalars ℤ)
  rw [hc] at h1
  have hinj : Function.Injective (algebraMap ℂ (Module.End ℂ V)) :=
    FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V)
  exact (isIntegral_algebraMap_iff hinj).mp h1

variable [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The **class sum** of `g`: the sum of `single x 1` over the conjugacy class of `g` in `ℂ[G]`. -/
noncomputable def classSum (g : G) : MonoidAlgebra ℂ G :=
  ∑ x ∈ Finset.univ.filter (fun x => IsConj g x), MonoidAlgebra.single x (1 : ℂ)

/-- The class sum is integral over `ℤ`: it is the image of the corresponding element of `ℤ[G]`
(integral over `ℤ`, since `ℤ[G]` is module-finite over `ℤ`) under the coefficient map `ℤ → ℂ`. -/
theorem classSum_isIntegral (g : G) : IsIntegral ℤ (classSum g) := by
  haveI : Module.Finite ℤ (MonoidAlgebra ℤ G) := Module.Finite.of_basis (Finsupp.basisSingleOne)
  set z : MonoidAlgebra ℤ G :=
    ∑ x ∈ Finset.univ.filter (fun x => IsConj g x), MonoidAlgebra.single x (1 : ℤ) with hz_def
  have hz : IsIntegral ℤ z := Algebra.IsIntegral.isIntegral z
  have hmap : MonoidAlgebra.mapAlgHom G (Algebra.ofId ℤ ℂ) z = classSum g := by
    rw [hz_def, classSum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MonoidAlgebra.mapAlgHom_single]
    simp
  rw [← hmap]
  exact hz.map (MonoidAlgebra.mapAlgHom G (Algebra.ofId ℤ ℂ))

/-- The class sum is central in `ℂ[G]`: conjugation by `k` permutes the conjugacy class. -/
theorem classSum_central (g k : G) :
    MonoidAlgebra.single k (1 : ℂ) * classSum g = classSum g * MonoidAlgebra.single k 1 := by
  unfold classSum
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [MonoidAlgebra.single_mul_single, mul_one]
  refine Finset.sum_nbij' (fun x => k * x * k⁻¹) (fun y => k⁻¹ * y * k) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hx).2.trans (isConj_iff.mpr ⟨k, rfl⟩)⟩
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hy).2.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)⟩
  · intro x _; group
  · intro y _; group
  · intro x _; congr 1; group

/-- The operator `ρ(classSum g)` commutes with the whole `G`-action (centrality of the class sum). -/
theorem asAlgebraHom_classSum_comm (ρ : Representation ℂ G V) (g k : G) (v : V) :
    (ρ.asAlgebraHom (classSum g)) (ρ k v) = ρ k ((ρ.asAlgebraHom (classSum g)) v) := by
  have hk : ρ k = ρ.asAlgebraHom (MonoidAlgebra.single k 1) :=
    (Representation.asAlgebraHom_single_one ρ k).symm
  have key : ρ.asAlgebraHom (classSum g) * ρ k = ρ k * ρ.asAlgebraHom (classSum g) := by
    rw [hk, ← map_mul, ← map_mul, classSum_central]
  have h2 := congr($key v)
  rw [Module.End.mul_apply, Module.End.mul_apply] at h2
  exact h2

/-- Trace of `ρ(classSum g)` is `(class size)·χ(g)`, since `χ` is constant on the conjugacy class. -/
theorem trace_asAlgebraHom_classSum (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] (g : G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum g))
      = ((Finset.univ.filter (fun x => IsConj g x)).card : ℂ) * ρ.character g := by
  unfold classSum
  rw [map_sum]
  simp only [Representation.asAlgebraHom_single_one]
  rw [map_sum]
  have : ∀ x ∈ Finset.univ.filter (fun x => IsConj g x),
      LinearMap.trace ℂ V (ρ x) = ρ.character g := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp (Finset.mem_filter.mp hx).2
    rw [← hc]
    exact ρ.char_conj g c
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

/-- **Central character integrality (ingredient 2/6).** For a finite group, an irreducible complex
representation `ρ`, and `g : G`, the number `(class size of g)·χ(g)/χ(1)` is an algebraic integer.

This is the central-character map evaluated at the class sum: by Schur, `ρ(classSum g) = c • 1`, and
taking traces gives `c·χ(1) = (class size)·χ(g)`, so `c = (class size)·χ(g)/χ(1)`; `c` is integral
over `ℤ` because the class sum is.  (The class size here is the cardinality of the conjugacy class,
i.e. `[G : C_G(g)]` — see `Burnside.lean` for the orbit–stabilizer identification.) -/
theorem classSize_char_isIntegral (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    [ρ.IsIrreducible] [Nontrivial V] (g : G) :
    IsIntegral ℤ (((Finset.univ.filter (fun x => IsConj g x)).card : ℂ)
      * ρ.character g / ρ.character 1) := by
  obtain ⟨c, hc, hcint⟩ := exists_scalar_isIntegral_of_central ρ (classSum g)
    (asAlgebraHom_classSum_comm ρ g) (classSum_isIntegral g)
  have htr : LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum g)) = c * ρ.character 1 := by
    rw [hc, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, LinearMap.trace_one, ρ.char_one]
  have htr2 := trace_asAlgebraHom_classSum ρ g
  rw [htr] at htr2
  have hne : ρ.character 1 ≠ 0 := by
    rw [ρ.char_one]; exact_mod_cast (Module.finrank_pos).ne'
  have heq : ((Finset.univ.filter (fun x => IsConj g x)).card : ℂ) * ρ.character g
      / ρ.character 1 = c := (div_eq_iff hne).mpr htr2.symm
  rw [heq]; exact hcint

/-- The conjugacy-class size of `g` equals the centralizer index `[G : C_G(g)]`
(orbit–stabilizer for the conjugation action of `ConjAct G`). -/
theorem filter_isConj_card_eq_index (g : G) :
    (Finset.univ.filter (fun x => IsConj g x)).card
      = (Subgroup.centralizer ({g} : Set G)).index := by
  have hset : (Finset.univ.filter (fun x => IsConj g x))
      = (MulAction.orbit (ConjAct G) g).toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      ConjAct.mem_orbit_conjAct]
    exact isConj_comm
  rw [hset, Set.toFinset_card]
  have hpos : 0 < Fintype.card (Subgroup.centralizer ({g} : Set G)) := Fintype.card_pos
  have hstab : Fintype.card (MulAction.stabilizer (ConjAct G) g)
      = Fintype.card (Subgroup.centralizer ({g} : Set G)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have hcardConj : Fintype.card (ConjAct G) = Fintype.card G := rfl
  have hcard_orbit : Fintype.card (MulAction.orbit (ConjAct G) g)
      * Fintype.card (Subgroup.centralizer ({g} : Set G)) = Fintype.card G := by
    rw [← hstab, MulAction.card_orbit_mul_card_stabilizer_eq_card_group, hcardConj]
  have hidx2 : (Subgroup.centralizer ({g} : Set G)).index
      * Fintype.card (Subgroup.centralizer ({g} : Set G)) = Fintype.card G := by
    have h := Subgroup.card_mul_index (Subgroup.centralizer ({g} : Set G))
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rw [mul_comm]; exact h
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hcard_orbit, hidx2])

/-- **Central character integrality, in Burnside's form.** For a finite group, an irreducible
complex representation `ρ`, and `g : G`, the number `[G : C_G(g)]·χ(g)/χ(1)` is an algebraic
integer — exactly the input needed for Burnside's prime-power class-size lemma. -/
theorem centralizerIndex_char_isIntegral (ρ : Representation ℂ G V) [FiniteDimensional ℂ V]
    [ρ.IsIrreducible] [Nontrivial V] (g : G) :
    IsIntegral ℤ (((Subgroup.centralizer ({g} : Set G)).index : ℂ)
      * ρ.character g / ρ.character 1) := by
  have h := classSize_char_isIntegral ρ g
  rwa [filter_isConj_card_eq_index] at h

end CentralCharacter

end FiniteSimpleGroups

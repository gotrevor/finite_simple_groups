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
3. **Column orthogonality** `∑_χ χ(1) χ(g) = 0` for `g ≠ 1`.  🔶 Route B (regular character) keystone
   built: `exists_wedderburn_character_decomp` gives `χ_reg(g) = ∑ᵢ dᵢ·χᵢ(g)` via Artin–Wedderburn
   `ℂ[G] ≃ₐ ∏ᵢ Mₐᵢ(ℂ)`, modulo the one self-contained trace lemma `trace_mulLeft_pi_matrix` (out at
   Aristotle).  With `character_leftRegular_eq` this yields `∑ᵢ dᵢ·χᵢ(g) = 0` for `g ≠ 1`.  Still to
   build for the Burnside endgame: irreducibility of the `Rᵢ` and trivial-multiplicity `= 1`.
4. **Kronecker's theorem** — an algebraic integer all of whose conjugates lie in the closed unit
   disc is `0` or a root of unity.  ✅ already in mathlib
   (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`).
5. **`-1/p` is not an algebraic integer.**  ✅ easy (`ℤ` integrally closed in `ℚ`); recorded here
   as `not_isIntegral_neg_inv_prime`.
6. **Scalar ⟹ proper normal subgroup**, contradicting simplicity.  ✅ fully proved here
   (`scalarSubgroup`, `scalarSubgroup_normal`, `comm_of_scalarSubgroup_eq_top`, and the final
   contradiction `not_isScalar_of_isSimpleGroup_of_nonabelian`).

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

/-- **Coprime-denominator integrality.**  If `m·β` and `n·β` are algebraic integers and `m, n` are
coprime naturals, then `β` is an algebraic integer.  (Bézout: `a·m + b·n = 1`, so
`β = a·(m·β) + b·(n·β)` is a `ℤ`-combination of algebraic integers.)  In the Burnside endgame, with
`m = [G:C_G(g)] = pᵏ` and `n = χ(1)` coprime (`p ∤ χ(1)`), this upgrades ingredient 2
(`[G:C_G(g)]·χ(g)/χ(1) ∈ ℤ̄`) together with `χ(g) ∈ ℤ̄` to `χ(g)/χ(1) ∈ ℤ̄`. -/
theorem isIntegral_of_coprime_smul {β : ℂ} {m n : ℕ} (hcop : Nat.Coprime m n)
    (hm : IsIntegral ℤ ((m : ℂ) * β)) (hn : IsIntegral ℤ ((n : ℂ) * β)) :
    IsIntegral ℤ β := by
  have hco : IsCoprime (m : ℤ) (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hcop)
  obtain ⟨a, b, hab⟩ := hco
  have h1 : (a : ℂ) * (m : ℂ) + (b : ℂ) * (n : ℂ) = 1 := by exact_mod_cast hab
  have hsum : (a : ℂ) * ((m : ℂ) * β) + (b : ℂ) * ((n : ℂ) * β) = β := by
    linear_combination β * h1
  have ha : IsIntegral ℤ (a : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := a))
  have hb : IsIntegral ℤ (b : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := b))
  rw [← hsum]
  exact (ha.mul hm).add (hb.mul hn)

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

/-- **Ingredient 6/6, completed.**  In a *nonabelian simple* group, no nontrivial element acts as a
scalar in a faithful representation `ρ`.  Indeed the scalar elements form a normal subgroup
(`scalarSubgroup_normal`); a nontrivial scalar makes it `≠ ⊥`, so by simplicity it is `⊤`, whence
`comm_of_scalarSubgroup_eq_top` forces `G` abelian — contradiction.

This is the final contradiction in Burnside's prime-power class-size lemma: once a nontrivial
element `g` is shown to act as a scalar in some faithful nontrivial irreducible representation
(via ingredients 1–5 + the vanishing lemma), simplicity is violated. -/
theorem not_isScalar_of_isSimpleGroup_of_nonabelian (ρ : Representation ℂ G V)
    (hfaith : Function.Injective ρ) (hsimple : IsSimpleGroup G)
    (hnonab : ¬ ∀ a b : G, a * b = b * a)
    (g : G) (hg : g ≠ 1) (c : ℂ) (hc : ρ g = algebraMap ℂ (Module.End ℂ V) c) : False := by
  haveI := hsimple
  have hmem : g ∈ scalarSubgroup ρ := ⟨c, hc⟩
  have hne : scalarSubgroup ρ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hmem
    exact hg hmem
  have htop : scalarSubgroup ρ = ⊤ :=
    (hsimple.eq_bot_or_eq_top_of_normal _ (scalarSubgroup_normal ρ)).resolve_left hne
  exact hnonab (comm_of_scalarSubgroup_eq_top ρ htop hfaith)

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

/-! ### Toward ingredient 3: the regular character

The regular representation `leftRegular ℂ G = ofMulAction ℂ G G` decomposes as `⊕_χ V_χ^{χ(1)}`, so
its character is `χ_reg = ∑_χ χ(1)·χ`.  Evaluated at `g ≠ 1`, `χ_reg(g) = 0` (a permutation
representation with no fixed points), which is exactly **column orthogonality** `∑_χ χ(1)χ(g) = 0`.

This lemma supplies the elementary half — the value of `χ_reg` — independent of the (still missing)
decomposition over the finite family of irreducibles.  The trace of a permutation representation is
its fixed-point count; for left multiplication `g·x = x ⟺ g = 1`, so `χ_reg(g) = |G|·[g = 1]`. -/

section RegularCharacter

open Representation
open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

/-- **The character of the regular representation** is `χ_reg(g) = |G|·[g = 1]`: the trace of the
permutation matrix of left multiplication by `g`, whose fixed points are `{x : g·x = x} = ∅` unless
`g = 1`.  When the regular-representation decomposition `χ_reg = ∑_χ χ(1)·χ` becomes available, this
yields column orthogonality (ingredient 3). -/
theorem character_leftRegular_eq (g : G) :
    (Representation.ofMulAction ℂ G G).character g
      = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne (R := ℂ) (ι := G))]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply, Finsupp.coe_basisSingleOne]
  have key : ∀ x : G, (Representation.ofMulAction ℂ G G g (Finsupp.single x 1)) x
      = if g = 1 then (1 : ℂ) else 0 := by
    intro x
    rw [Representation.ofMulAction]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, smul_eq_mul, Finsupp.single_apply]
    by_cases hg1 : g = 1
    · subst hg1; simp
    · rw [if_neg (fun h => hg1 (mul_eq_right.mp h)), if_neg hg1]
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero]

/-- Since `χ_reg` is supported at the identity, `∑ g, χ_reg(g)·f(g) = |G|·f(1)` for any
`f : G → ℂ`.  Taking `f(g) = χ(g⁻¹)` (or `conj χ(g)`) computes the multiplicity of an irreducible
`χ` in the regular representation as `⟨χ_reg, χ⟩ = χ(1)` — the second half of the regular-character
decomposition `χ_reg = ∑_χ χ(1)·χ` (ingredient 3, Route B). -/
theorem sum_character_leftRegular_mul (f : G → ℂ) :
    ∑ g, (Representation.ofMulAction ℂ G G).character g * f g = (Fintype.card G : ℂ) * f 1 := by
  simp only [character_leftRegular_eq, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ 1 (fun g => (Fintype.card G : ℂ) * f g)]
  simp

end RegularCharacter

/-! ### Toward ingredient 3: the Artin–Wedderburn count

`ℂ[G]` is semisimple (Maschke) and finite-dimensional, so over the algebraically closed field `ℂ`
it decomposes as `ℂ[G] ≃ₐ[ℂ] ∏ᵢ Matrix (Fin dᵢ) (Fin dᵢ) ℂ` (mathlib's
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`).  The number of factors `n` is the
number of irreducible characters `#Irr(G)`, and the `dᵢ` are the irreducible degrees `χᵢ(1)`.
Comparing `ℂ`-dimensions gives the classical relation `∑ᵢ dᵢ² = |G|`.

This is the structural backbone for the finite family `Irr(G)` that column orthogonality
(ingredient 3, Route B) needs. -/

section Wedderburn

variable {G : Type*} [Group G] [Fintype G]

/-- **`∑ dᵢ² = |G|`** from Artin–Wedderburn for `ℂ[G]`: there are finitely many irreducible degrees
`dᵢ` (`= χᵢ(1)`, one per matrix factor of `ℂ[G] ≃ₐ ∏ᵢ Mₐᵢ(ℂ)`) and the sum of their squares is the
group order.  Gives the finite index set and the dimension count underlying `Irr(G)`. -/
theorem sum_sq_dim_eq_card :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧ ∑ i, (d i) ^ 2 = Fintype.card G := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (Finsupp.basisSingleOne)
  let b : Module.Basis G ℂ (MonoidAlgebra ℂ G) := Finsupp.basisSingleOne
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed (R := MonoidAlgebra ℂ G) (F := ℂ)
  refine ⟨n, d, hd, ?_⟩
  have hfin : Module.finrank ℂ (MonoidAlgebra ℂ G)
      = Module.finrank ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_eq_card_basis b, Module.finrank_pi_fintype] at hfin
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hfin
  rw [hfin]
  exact Finset.sum_congr rfl fun i _ => pow_two (d i)

end Wedderburn

/-! ### Toward the scalar step: equality case of the triangle inequality

After Burnside's vanishing lemma (`burnside_vanishing_core`, out at Aristotle) gives
`χ(g) = 0 ∨ ‖χ(g)‖ = χ(1)`, the scalar case `‖χ(g)‖ = χ(1)` must be converted to "`g` acts as a
scalar".  Since `χ(g)` is the sum of the `χ(1)` eigenvalues of `ρ g` (all roots of unity, modulus
`1`), `‖χ(g)‖ = χ(1)` is exactly the equality case of the triangle inequality, forcing all
eigenvalues equal — whence `ρ g` (diagonalizable, as it has finite order) is a scalar.  This lemma
is the analytic equality-case half. -/

/-- **Equality case of the triangle inequality for unit vectors.**  If `card ι` complex numbers of
modulus `1` sum to something of modulus `card ι`, they are all equal. -/
theorem eq_of_norm_sum_eq_card {ι : Type*} [Fintype ι] (ζ : ι → ℂ)
    (h1 : ∀ i, ‖ζ i‖ = 1) (hsum : ‖∑ k, ζ k‖ = Fintype.card ι) (i j : ι) :
    ζ i = ζ j := by
  classical
  set S := ∑ k, ζ k with hS
  have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hSnorm_pos : 0 < ‖S‖ := by rw [hsum]; exact_mod_cast hcard_pos
  have hSne : S ≠ 0 := by intro h; rw [h, norm_zero] at hSnorm_pos; exact lt_irrefl _ hSnorm_pos
  have hconjne : (starRingEnd ℂ) S ≠ 0 := by simpa using hSne
  have hnorm : ∀ k, ‖(starRingEnd ℂ) S * ζ k‖ = ‖S‖ := by
    intro k; rw [norm_mul, RCLike.norm_conj, h1 k, mul_one]
  have hre_le : ∀ k, ((starRingEnd ℂ) S * ζ k).re ≤ ‖S‖ := by
    intro k
    calc ((starRingEnd ℂ) S * ζ k).re ≤ ‖(starRingEnd ℂ) S * ζ k‖ := Complex.re_le_norm _
      _ = ‖S‖ := hnorm k
  have hre_sum : ∑ k, ((starRingEnd ℂ) S * ζ k).re = ‖S‖ * ‖S‖ := by
    have h0 : (starRingEnd ℂ) S * S = ((Complex.normSq S : ℝ) : ℂ) := by
      rw [mul_comm]; exact Complex.mul_conj S
    rw [← Complex.re_sum, ← Finset.mul_sum, ← hS, h0, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
    ring
  have hbound_sum : ∑ _k : ι, ‖S‖ = ‖S‖ * ‖S‖ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum]
  have heq_each : ∀ k ∈ Finset.univ, ((starRingEnd ℂ) S * ζ k).re = ‖S‖ := by
    have hsum_eq : ∑ k, ((starRingEnd ℂ) S * ζ k).re = ∑ _k : ι, ‖S‖ := by
      rw [hre_sum, hbound_sum]
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hre_le k)).mp hsum_eq
  have hval : ∀ k, (starRingEnd ℂ) S * ζ k = (‖S‖ : ℂ) := by
    intro k
    have hre : ((starRingEnd ℂ) S * ζ k).re = ‖S‖ := heq_each k (Finset.mem_univ k)
    have hnsq : ((starRingEnd ℂ) S * ζ k).re * ((starRingEnd ℂ) S * ζ k).re
        + ((starRingEnd ℂ) S * ζ k).im * ((starRingEnd ℂ) S * ζ k).im = ‖S‖ * ‖S‖ := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hnorm k, pow_two]
    rw [hre] at hnsq
    have him : ((starRingEnd ℂ) S * ζ k).im * ((starRingEnd ℂ) S * ζ k).im = 0 := by linarith
    apply Complex.ext
    · rw [hre, Complex.ofReal_re]
    · rw [Complex.ofReal_im]; exact mul_self_eq_zero.mp him
  have : (starRingEnd ℂ) S * ζ i = (starRingEnd ℂ) S * ζ j := by rw [hval i, hval j]
  exact mul_left_cancel₀ hconjne this

/-- **Burnside's vanishing lemma (analytic core).**  If `s = ∑ i, ζ i` is a sum of `d ≥ 1` roots of
unity in `ℂ`, and `s / d` is an algebraic integer, then either `s = 0` or `‖s‖ = d`.

With `d = χ(1)` the degree and `ζ i` the eigenvalues of `ρ g` (roots of unity), `s = χ(g)` and the
hypothesis `IsIntegral ℤ (χ(g)/χ(1))` (from ingredient 2 + a gcd argument) forces `χ(g) = 0` or
`‖χ(g)‖ = χ(1)`.

Proof (number field + Kronecker): the `ζ i` generate a number field `K`; `β = s/d ∈ K` is integral
over `ℤ`; every embedding `K →+* ℂ` sends `β` to an average of roots of unity, of norm `≤ 1`; by
Kronecker (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`) `β = 0` or `β` is a root of unity
(`‖β‖ = 1`), giving `s = 0` or `‖s‖ = d`.

Discharged by Aristotle (Harmonic) job `8451c8e2`, then re-verified in this kernel and confirmed
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`). -/
theorem burnside_vanishing_core {d : ℕ} (hd : 1 ≤ d) (ζ : Fin d → ℂ)
    (hζ : ∀ i, ∃ k : ℕ, 1 ≤ k ∧ ζ i ^ k = 1)
    (hint : IsIntegral ℤ ((∑ i, ζ i) / d)) :
    (∑ i, ζ i) = 0 ∨ ‖∑ i, ζ i‖ = d := by
  set s := ∑ i, ζ i with hs_def
  set β := s / (d : ℂ) with hβ_def
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have norm_of_pow_eq_one : ∀ (z : ℂ) (k : ℕ), 1 ≤ k → z ^ k = 1 → ‖z‖ = 1 := by
    intro z k hk hz
    have h1 : ‖z‖ ^ k = 1 := by rw [← norm_pow, hz, norm_one]
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · exact absurd (pow_lt_one₀ (norm_nonneg z) h (show k ≠ 0 by omega)) (by linarith)
    · exact h
    · exact absurd (one_lt_pow₀ h (show k ≠ 0 by omega)) (by linarith)
  have hζ_norm : ∀ i, ‖ζ i‖ = 1 := by
    intro i; obtain ⟨k, hk, hz⟩ := hζ i; exact norm_of_pow_eq_one _ k hk hz
  set K := IntermediateField.adjoin ℚ (Set.range ζ)
  have halg : ∀ x ∈ Set.range ζ, IsIntegral ℚ x := by
    rintro x ⟨i, rfl⟩; obtain ⟨k, hk, hz⟩ := hζ i
    exact (show IsIntegral ℤ (ζ i) from
      ⟨Polynomial.X ^ k - 1,
       (Polynomial.monic_X_pow k).sub_of_left
         (by rw [Polynomial.degree_one, Polynomial.degree_X_pow]; exact_mod_cast by omega),
       by simp [hz]⟩).tower_top
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin halg
  haveI : NumberField K :=
    { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hmem : ∀ i, ζ i ∈ K := fun i =>
    IntermediateField.subset_adjoin ℚ (Set.range ζ) (Set.mem_range_self i)
  set ζ_K : Fin d → K := fun i => ⟨ζ i, hmem i⟩
  set β_K : K := (∑ i, ζ_K i) / (d : K)
  have hζ_val : ∀ i, K.val (ζ_K i) = ζ i := fun _ => rfl
  have hβ_map : K.val β_K = β := by
    simp only [β_K, map_div₀, map_sum, map_natCast, hζ_val]; exact hβ_def.symm
  have hint_K : IsIntegral ℤ β_K := by
    have h : IsIntegral ℤ (IsScalarTower.toAlgHom ℤ K ℂ β_K) := by
      show IsIntegral ℤ (K.val β_K); rwa [hβ_map]
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K ℂ)
      (IsScalarTower.toAlgHom ℤ K ℂ).injective).mp h
  have hembed : ∀ φ : K →+* ℂ, ‖φ β_K‖ ≤ 1 := by
    intro φ
    have hφ_β : φ β_K = (∑ i, φ (ζ_K i)) / (d : ℂ) := by
      simp [β_K, map_sum, map_div₀, map_natCast]
    have hφ_norm : ∀ i, ‖φ (ζ_K i)‖ = 1 := by
      intro i; obtain ⟨k, hk, hz⟩ := hζ i
      have hζK_pow : (ζ_K i) ^ k = 1 := Subtype.ext (by simp [ζ_K, hz])
      exact norm_of_pow_eq_one _ k hk (by rw [← map_pow, hζK_pow, map_one])
    rw [hφ_β, norm_div, Complex.norm_natCast, div_le_one hd_pos]
    calc ‖∑ i, φ (ζ_K i)‖ ≤ ∑ i, ‖φ (ζ_K i)‖ := norm_sum_le _ _
      _ = ∑ _i : Fin d, (1 : ℝ) := by congr 1; ext i; exact hφ_norm i
      _ = d := by simp
  by_cases hβ0 : β_K = 0
  · left
    have : β = 0 := by rw [← hβ_map]; simp [hβ0]
    rwa [hβ_def, div_eq_zero_iff, or_iff_left hd_ne] at this
  · right
    obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hβ0 hint_K hembed
    have hβ_pow : β ^ n = 1 := by
      have := congr_arg K.val hpow
      simp only [map_pow, map_one, hβ_map] at this; exact this
    have hβ_norm : ‖β‖ = 1 := norm_of_pow_eq_one _ n (by omega) hβ_pow
    have hsβ : s = (d : ℂ) * β := by rw [hβ_def, mul_div_cancel₀ s hd_ne]
    rw [hsβ, norm_mul, Complex.norm_natCast, hβ_norm, mul_one]

/-! ### Regular-character decomposition via Artin–Wedderburn (ingredient 3, Route B)

`ℂ[G]` is semisimple (Maschke), finite-dimensional, over the algebraically closed field `ℂ`, so
`ℂ[G] ≃ₐ[ℂ] ∏ᵢ Matrix (Fin dᵢ) (Fin dᵢ) ℂ` (Wedderburn).  The `i`-th projection of the basis element
`single g 1` gives an irreducible matrix representation `Rᵢ : G →* Matrix (Fin dᵢ) (Fin dᵢ) ℂ` with
character `χᵢ(g) = trace(Rᵢ g)` and degree `dᵢ = χᵢ(1)`.  Pushing the regular character through `e`,
splitting the trace over the product, and using `trace(mulLeft A) = d · trace A` on each matrix
factor yields the **regular-character decomposition**

  `χ_reg(g) = ∑ᵢ dᵢ · χᵢ(g)`.

Combined with `character_leftRegular_eq` (`χ_reg(g) = |G|·[g=1]`), this gives the column-orthogonality
relation `∑ᵢ dᵢ·χᵢ(g) = 0` for `g ≠ 1` that the Burnside endgame consumes (ingredient 3). -/

open LinearMap in
/-- **Trace of left-multiplication on a product of matrix algebras.**  For `M = (Mᵢ)ᵢ` in the
`ℂ`-algebra `∏ᵢ Matrix (Fin dᵢ) (Fin dᵢ) ℂ`, the trace of "left multiply by `M`" is
`∑ᵢ dᵢ · trace(Mᵢ)`.  Left-multiplication is block-diagonal across the product, and on a single
`d×d` matrix algebra `trace(mulLeft A) = d · trace A`.

Discharged by Aristotle (Harmonic) job `eed8a149-2866-41a9-8086-f6f7ff10c1dc`, then re-verified in
this v4.29.1 kernel and confirmed `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).
The proof: split the trace over the product via the `Pi.basis` of `Matrix.stdBasis` factors, then on
each factor the matrix of `mulLeft A` in the standard basis has entries `A p r · δ(q,s)` whose
diagonal sum is `d · trace A`. -/
theorem trace_mulLeft_pi_matrix {n : ℕ} (d : Fin n → ℕ)
    (M : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
        (LinearMap.mulLeft ℂ M)
      = ∑ i, (d i : ℂ) * (M i).trace := by
  have h_trace_prod : (LinearMap.trace ℂ ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) (mulLeft ℂ M) = ∑ i, (LinearMap.trace ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) (mulLeft ℂ (M i)) := by
    have h_trace_prod : ∀ (f : (i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ] Matrix (Fin (d i)) (Fin (d i)) ℂ), (LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) = ∑ i, (LinearMap.trace ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) (f i) := by
      intro f
      have h_trace_direct_sum : ∀ (f : (i : Fin n) → (Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ] (Matrix (Fin (d i)) (Fin (d i)) ℂ)), (LinearMap.trace ℂ ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) (pi fun i => f i ∘ₗ (LinearMap.proj i)) = ∑ i, (LinearMap.trace ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) (f i) := by
        intro f
        have h_iso : (LinearMap.trace ℂ ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) = (LinearMap.trace ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
          rfl
        rw [ h_iso, LinearMap.trace_eq_matrix_trace ℂ ( Pi.basis fun i => Matrix.stdBasis ℂ ( Fin ( d i ) ) ( Fin ( d i ) ) ) ]
        simp +decide [ LinearMap.trace_eq_matrix_trace ℂ ( Matrix.stdBasis ℂ ( Fin ( d _ ) ) ( Fin ( d _ ) ) ) ]
        simp +decide [ Matrix.trace, toMatrix_apply ]
        rw [ Finset.sum_sigma' ]
        rfl
      exact h_trace_direct_sum f
    convert h_trace_prod ( fun i => mulLeft ℂ ( M i ) ) using 1
  have h_trace_mulLeft : ∀ (i : Fin n) (A : Matrix (Fin (d i)) (Fin (d i)) ℂ), (LinearMap.trace ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) (mulLeft ℂ A) = (d i : ℂ) * A.trace := by
    intro i A
    set basis : Module.Basis (Fin (d i) × Fin (d i)) ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) := Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i))
    rw [ LinearMap.trace_eq_matrix_trace ℂ basis ]
    have h_entry : ∀ (p q r s : Fin (d i)), ((toMatrix basis basis) (mulLeft ℂ A)) (p, q) (r, s) = A p r * (if q = s then 1 else 0) := by
      intro p q r s; simp +decide [ toMatrix_apply, Matrix.mul_apply ]
      simp +decide [ basis, Matrix.mul_apply, stdBasis ]
      rw [ Finset.sum_eq_single r ] <;> aesop
    simp +decide [ h_entry, Matrix.trace ]
    erw [ Finset.sum_congr rfl fun x hx => h_entry _ _ _ _ ] ; simp +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ]
    erw [ Finset.sum_product ] ; simp +decide [ Finset.mul_sum _ _ _ ]
  aesop

/-- For an algebra equivalence `e`, conjugating left-multiplication by `x` gives left-multiplication
by `e x`: `e.conj (mulLeft x) = mulLeft (e x)`.  (Used to push the regular character through the
Wedderburn isomorphism via `LinearMap.trace_conj'`.) -/
theorem conj_mulLeft {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) (x : A) :
    e.toLinearEquiv.conj (LinearMap.mulLeft ℂ x) = LinearMap.mulLeft ℂ (e x) := by
  refine LinearMap.ext fun y => ?_
  simp only [LinearEquiv.conj_apply_apply, LinearMap.mulLeft_apply, AlgEquiv.toLinearEquiv_apply,
    map_mul]
  congr 1
  exact e.apply_symm_apply y

/-- **Simplicity transfers along a surjective ring hom with compatible actions.**  If `f : R →+* S`
is surjective and the `R`- and `S`-actions on `M` agree through `f` (`r • m = f r • m`), then `M` is
a simple `R`-module whenever it is a simple `S`-module.  (The identity is a bijective `f`-semilinear
map.)

For the Wedderburn factor `Rᵢ`: with `R = ℂ[G]`, `S = End ℂ (Fin dᵢ → ℂ)`, `f = Rᵢ.asAlgebraHom`
surjective, this reduces `IsIrreducible (repOfMatrixHom Rᵢ)` (i.e. `IsSimpleModule ℂ[G] ·.asModule`)
to `IsSimpleModule (End ℂ (Fin dᵢ → ℂ)) (Fin dᵢ → ℂ)` (the natural module is simple; Aristotle
`dc41262f` proves the `Matrix` form). -/
theorem isSimpleModule_of_ringHom_surjective {R S M : Type*} [Ring R] [Ring S] [AddCommGroup M]
    [Module R M] [Module S M] (f : R →+* S) (hf : Function.Surjective f)
    (hcompat : ∀ (r : R) (m : M), r • m = f r • m) [IsSimpleModule S M] :
    IsSimpleModule R M := by
  haveI : RingHomSurjective f := ⟨hf⟩
  let l : M →ₛₗ[f] M :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun r m => hcompat r m }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mpr ‹_›

/-- **The natural module `Fin d → ℂ` of the full matrix algebra is simple** (for `d > 0`).  Any
nonzero submodule contains a vector `v` with some `vᵢ ≠ 0`; a rank-one matrix maps `v` to any target
`w`, so the submodule is everything.  Discharged by Aristotle (Harmonic) job
`dc41262f-321e-4bf9-a161-7e1be4320f4c`, re-verified in this kernel and `#print axioms`-clean.

Composed with `isSimpleModule_of_ringHom_surjective` (and `End ℂ V ≅ Matrix`) this gives the
irreducibility of any representation whose `asAlgebraHom` is surjective — in particular each
Wedderburn factor `Rᵢ`. -/
theorem isSimpleModule_natural_matrix {d : ℕ} (hd : 0 < d) :
    IsSimpleModule (Matrix (Fin d) (Fin d) ℂ) (Fin d → ℂ) := by
  refine' { .. }
  · refine' ⟨ ⊥, ⊤, _ ⟩
    simp +decide [ Submodule.eq_top_iff' ]
    exact ⟨ fun _ => 1, fun h => by simpa using congr_fun h ⟨ 0, hd ⟩ ⟩
  · intro M
    by_cases hM : M = ⊥
    · exact Or.inl hM
    · exact Or.inr (by
      obtain ⟨ v, hv ⟩ := ( Submodule.ne_bot_iff _ ).mp hM
      obtain ⟨ i, hi ⟩ : ∃ i : Fin d, v i ≠ 0 := Function.ne_iff.mp hv.2
      refine' eq_top_iff.mpr fun w hw => _
      convert M.smul_mem ( Matrix.of ( fun j k => if k = i then w j / v i else 0 ) ) hv.1 using 1
      ext j
      simp +decide [ Matrix.mulVec, dotProduct, Finset.sum_ite, Finset.filter_eq',
        Finset.filter_ne', hi ])

/-- **A nontrivial homomorphism out of a simple group is injective.**  Its kernel is a proper
normal subgroup, hence `⊥` by simplicity.  Applied to a nontrivial Wedderburn-factor representation
`Rᵢ : G →* Mₐᵢ(ℂ)` of a simple `G`, this gives the faithfulness that ingredient 6
(`not_isScalar_of_isSimpleGroup_of_nonabelian`) consumes. -/
theorem injective_of_isSimpleGroup_of_exists_ne {G H : Type*} [Group G] [IsSimpleGroup G]
    [Monoid H] (φ : G →* H) (hφ : ∃ g, φ g ≠ 1) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker φ.normal_ker with h | h
  · exact h
  · exfalso
    obtain ⟨g, hg⟩ := hφ
    have hmem : g ∈ φ.ker := by rw [h]; exact Subgroup.mem_top g
    exact hg (MonoidHom.mem_ker.mp hmem)

/-- **A nonabelian simple group is perfect:** `[G,G] = ⊤`.  The commutator subgroup is normal, so by
simplicity it is `⊥` or `⊤`; `⊥` would force `G` abelian (`commutator_eq_bot_iff_center_eq_top`),
contradicting nonabelianness.  Consequence (for gap 3, `T = 1`): `G^ab = 1`, so the trivial
representation is the only linear character, hence the unique `dᵢ = 1` Wedderburn factor. -/
theorem commutator_eq_top_of_isSimpleGroup_of_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ¬ ∀ a b : G, a * b = b * a) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with h | h
  · exfalso
    apply hnonab
    rw [commutator_eq_bot_iff_center_eq_top] at h
    intro a b
    have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a
  · exact h

/-- The `Representation ℂ G (Fin d → ℂ)` underlying a matrix homomorphism `R : G →* Mₐ(ℂ)`, via the
algebra equivalence `Matrix.toLinAlgEquiv' : Mₐ(ℂ) ≃ₐ End ℂ (Fin d → ℂ)`.  Lets the Wedderburn-factor
maps `Rᵢ` be fed to the `Representation`-level ingredients (2 and 6) of Burnside's lemma. -/
def repOfMatrixHom {G : Type*} [Group G] {d : ℕ}
    (R : G →* Matrix (Fin d) (Fin d) ℂ) : Representation ℂ G (Fin d → ℂ) where
  toFun := fun g => Matrix.toLinAlgEquiv' (R g)
  map_one' := by rw [R.map_one, map_one]
  map_mul' := fun g h => by rw [R.map_mul, map_mul]

/-- The character of `repOfMatrixHom R` at `g` is the matrix trace `trace (R g)` — so the Wedderburn
decomposition `χ_reg(g) = ∑ᵢ dᵢ·trace(Rᵢ g)` is literally `∑ᵢ dᵢ·χᵢ(g)` for the irreducible
characters `χᵢ = (repOfMatrixHom Rᵢ).character`. -/
theorem repOfMatrixHom_character {G : Type*} [Group G] {d : ℕ}
    (R : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    (repOfMatrixHom R).character g = (R g).trace := by
  rw [Representation.character]
  show LinearMap.trace ℂ (Fin d → ℂ) (Matrix.toLinAlgEquiv' (R g)) = (R g).trace
  rw [show (Matrix.toLinAlgEquiv' (R g) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) = (R g).toLin' from rfl]
  exact Matrix.trace_toLin'_eq (R g)

/-- Each Wedderburn-factor trace `trace(Rᵢ g)` is an algebraic integer (ingredient 1 applied to
`repOfMatrixHom Rᵢ`). -/
theorem trace_matrixHom_isIntegral {G : Type*} [Group G] [Finite G] {d : ℕ}
    (R : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) : IsIntegral ℤ (R g).trace := by
  rw [← repOfMatrixHom_character R g]
  exact Representation.character_isIntegral (repOfMatrixHom R) g

/-- Each Wedderburn-factor character is bounded by its degree: `‖trace(Rᵢ g)‖ ≤ dᵢ` (ingredient
`norm_character_le` via `repOfMatrixHom`).  This is the closed-unit-disc input to Kronecker. -/
theorem norm_trace_matrixHom_le {G : Type*} [Group G] [Finite G] {d : ℕ}
    (R : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) : ‖(R g).trace‖ ≤ (d : ℝ) := by
  rw [← repOfMatrixHom_character R g]
  have h := Representation.norm_character_le (repOfMatrixHom R) g
  rwa [show Module.finrank ℂ (Fin d → ℂ) = d by rw [Module.finrank_pi, Fintype.card_fin]] at h

/-- **`repOfMatrixHom R`'s algebra map factors through a surjective `Ψ`.**  If
`Ψ : ℂ[G] →ₐ Mₐ(ℂ)` satisfies `Ψ (single g 1) = R g`, then the representation's algebra map
`(repOfMatrixHom R).asAlgebraHom : ℂ[G] →ₐ End ℂ (Fin d → ℂ)` equals `toLinAlgEquiv' ∘ Ψ`.  (Both
sides are algebra homs agreeing on the generators `single g 1`.) -/
theorem repOfMatrixHom_asAlgebraHom_factor {G : Type*} [Group G] {d : ℕ}
    (R : G →* Matrix (Fin d) (Fin d) ℂ)
    (Ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΨ : ∀ g, Ψ (MonoidAlgebra.single g 1) = R g) :
    (repOfMatrixHom R).asAlgebraHom
      = (Matrix.toLinAlgEquiv' (n := Fin d) (R := ℂ)).toAlgHom.comp Ψ := by
  refine MonoidAlgebra.algHom_ext fun g => ?_
  rw [AlgHom.comp_apply, Representation.asAlgebraHom_single_one, hΨ]
  rfl

/-- **Irreducibility criterion (gap 1).**  A matrix representation `R : G →* Mₐ(ℂ)` (`d > 0`) arising
from a *surjective* algebra hom `Ψ : ℂ[G] →ₐ Mₐ(ℂ)` with `Ψ (single g 1) = R g` is irreducible.

The `ℂ[G]`-action on `(repOfMatrixHom R).asModule` factors as `ℂ[G] →(Ψ)→ Mₐ(ℂ) → End(Fin d → ℂ)`;
since `Ψ` is onto `Mₐ(ℂ)`, the `ℂ[G]`-invariant subspaces are exactly the `Mₐ(ℂ)`-invariant
subspaces of the natural module `Fin d → ℂ`, which are only `⊥` and `⊤`
(`isSimpleModule_natural_matrix`).  Formally: transfer simplicity along the surjection `Ψ`
(`isSimpleModule_of_ringHom_surjective`).  This discharges gap 1 for any Wedderburn factor, whose
`Ψ = πᵢ ∘ e` is surjective by `exists_wedderburn_character_decomp`. -/
theorem isIrreducible_of_surjective_algHom {G : Type*} [Group G] {d : ℕ} (hd : 0 < d)
    (R : G →* Matrix (Fin d) (Fin d) ℂ)
    (Ψ : MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΨsurj : Function.Surjective Ψ)
    (hΨ : ∀ g, Ψ (MonoidAlgebra.single g 1) = R g) :
    (repOfMatrixHom R).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hfact := repOfMatrixHom_asAlgebraHom_factor R Ψ hΨ
  haveI hsurj : RingHomSurjective Ψ.toRingHom := ⟨hΨsurj⟩
  -- The (identity) `asModuleEquiv : asModule → (Fin d → ℂ)` is `Ψ`-semilinear: the `ℂ[G]`-action
  -- factors through `Ψ` (`hfact`), so it agrees with the matrix mul-vec action pulled back along `Ψ`.
  let l : (repOfMatrixHom R).asModule →ₛₗ[Ψ.toRingHom] (Fin d → ℂ) :=
    { toFun := (repOfMatrixHom R).asModuleEquiv
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => by
        show (repOfMatrixHom R).asModuleEquiv (r • m)
            = Ψ.toRingHom r • (repOfMatrixHom R).asModuleEquiv m
        rw [Representation.asModuleEquiv_map_smul, hfact]; rfl }
  have hbij : Function.Bijective l := (repOfMatrixHom R).asModuleEquiv.bijective
  exact (@LinearMap.isSimpleModule_iff_of_bijective
      (MonoidAlgebra ℂ G) (Matrix (Fin d) (Fin d) ℂ) _ _
      ((repOfMatrixHom R).asModule) _
      (inferInstanceAs (Module (MonoidAlgebra ℂ G) ((repOfMatrixHom R).asModule)))
      (Fin d → ℂ) _ _ Ψ.toRingHom _ l hbij).mpr
    (isSimpleModule_natural_matrix hd)

section RegularDecomp

variable {G : Type*} [Group G] [Fintype G]

/-- The left-regular character `χ_reg(g)` is the trace of left-multiplication by `single g 1` on
`ℂ[G]`.  (`Representation.ofMulAction` on the group acting on itself is left multiplication.) -/
theorem character_ofMulAction_eq_trace_mulLeft {G : Type*} [Group G] (g : G) :
    (Representation.ofMulAction ℂ G G).character g
      = LinearMap.trace ℂ (MonoidAlgebra ℂ G)
          (LinearMap.mulLeft ℂ (MonoidAlgebra.single g (1 : ℂ))) := by
  rw [Representation.character]
  congr 1
  refine Finsupp.lhom_ext fun a b => ?_
  rw [Representation.ofMulAction_single]
  show MonoidAlgebra.single (g • a) b = MonoidAlgebra.single g 1 * MonoidAlgebra.single a b
  rw [MonoidAlgebra.single_mul_single, one_mul, smul_eq_mul]

/-- **Regular-character decomposition (ingredient 3, Route B).**  Via Artin–Wedderburn
`ℂ[G] ≃ₐ ∏ᵢ Mₐᵢ(ℂ)`, the left-regular character decomposes as `χ_reg(g) = ∑ᵢ dᵢ · trace(Rᵢ g)`
where `Rᵢ : G →* Mₐᵢ(ℂ)` is the `i`-th irreducible matrix representation (`g ↦ (e (single g 1)) i`)
and `dᵢ` (`= trace(Rᵢ 1)`) its degree.  With `character_leftRegular_eq` this gives column
orthogonality `∑ᵢ dᵢ·trace(Rᵢ g) = 0` for `g ≠ 1`. -/
theorem exists_wedderburn_character_decomp :
    ∃ (n : ℕ) (d : Fin n → ℕ) (R : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Ψ : ∀ i, MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin (d i)) (Fin (d i)) ℂ),
      (∀ i, NeZero (d i)) ∧
      (∀ i, R i 1 = 1) ∧
      (∀ i, Function.Surjective (Ψ i)) ∧
      (∀ i g, Ψ i (MonoidAlgebra.single g 1) = R i g) ∧
      (∀ g, (Representation.ofMulAction ℂ G G).character g
              = ∑ i, (d i : ℂ) * (R i g).trace) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (Finsupp.basisSingleOne)
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed (R := MonoidAlgebra ℂ G) (F := ℂ)
  have hone : e (MonoidAlgebra.single (1 : G) (1 : ℂ)) = 1 := by
    rw [← MonoidAlgebra.one_def, map_one]
  have hmul : ∀ g h : G, e (MonoidAlgebra.single (g * h) (1 : ℂ))
      = e (MonoidAlgebra.single g 1) * e (MonoidAlgebra.single h 1) := by
    intro g h
    rw [← map_mul, MonoidAlgebra.single_mul_single, one_mul]
  let R : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ := fun i =>
    { toFun := fun g => (e (MonoidAlgebra.single g 1)) i
      map_one' := by
        show (e (MonoidAlgebra.single (1 : G) (1 : ℂ))) i = 1
        rw [hone]; rfl
      map_mul' := fun g h => by
        show (e (MonoidAlgebra.single (g * h) (1 : ℂ))) i
           = (e (MonoidAlgebra.single g 1)) i * (e (MonoidAlgebra.single h 1)) i
        rw [hmul g h]; rfl }
  -- The `i`-th Wedderburn projection `πᵢ ∘ e : ℂ[G] →ₐ Mₐᵢ(ℂ)`, a surjective algebra hom whose
  -- value at `single g 1` is the matrix `Rᵢ g`.
  let Ψ : ∀ i, MonoidAlgebra ℂ G →ₐ[ℂ] Matrix (Fin (d i)) (Fin (d i)) ℂ := fun i =>
    (Pi.evalAlgHom ℂ (fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i).comp e.toAlgHom
  have hΨsurj : ∀ i, Function.Surjective (Ψ i) := fun i x => by
    obtain ⟨y, hy⟩ := e.surjective (Function.update 0 i x)
    refine ⟨y, ?_⟩
    have hval : Ψ i y = (e y) i := rfl
    rw [hval, hy, Function.update_self]
  have hΨR : ∀ i g, Ψ i (MonoidAlgebra.single g 1) = R i g := fun i g => rfl
  refine ⟨n, d, R, Ψ, hd, fun i => (R i).map_one, hΨsurj, hΨR, fun g => ?_⟩
  rw [character_ofMulAction_eq_trace_mulLeft g,
    ← LinearMap.trace_conj' (LinearMap.mulLeft ℂ (MonoidAlgebra.single g (1 : ℂ))) e.toLinearEquiv,
    conj_mulLeft e (MonoidAlgebra.single g 1), trace_mulLeft_pi_matrix d (e (MonoidAlgebra.single g 1))]
  rfl

end RegularDecomp

/-- **Burnside endgame, arithmetic core.**  Given complex numbers `aᵢ` summing to `0`, with one
distinguished index `i₀` where `a_{i₀} = 1` (the trivial character's contribution) and every other
`aᵢ = p·θᵢ` for an algebraic integer `θᵢ`, derive `False`.  Indeed `0 = 1 + p·(∑_{i≠i₀} θᵢ)` makes
`Θ = ∑ θᵢ = -1/p` an algebraic integer, contradicting `not_isIntegral_neg_inv_prime`.

This is the final assembly of Burnside's class-size lemma: instantiate `aᵢ = dᵢ·χᵢ(g)` from
`exists_wedderburn_character_decomp` (so `∑ aᵢ = χ_reg(g) = 0` for `g ≠ 1`), `i₀` = the unique
trivial factor (gap 3, `T = 1`), and for nontrivial factors split on `p ∣ dᵢ`: if `p ∤ dᵢ` then
`χᵢ(g) = 0` (gap 1 irreducibility + gap 2 scalar bridge ⇒ vanishing, so `aᵢ = 0 = p·0`); if `p ∣ dᵢ`
then `aᵢ = dᵢχᵢ(g) = p·((dᵢ/p)χᵢ(g))` with `(dᵢ/p)χᵢ(g) ∈ ℤ̄`. -/
theorem burnside_final_contradiction {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (p : ℕ) (hp : p.Prime)
    (i₀ : ι) (ha0 : a i₀ = 1)
    (θ : ι → ℂ) (hθ : ∀ i, i ≠ i₀ → a i = (p : ℂ) * θ i)
    (hθint : ∀ i, i ≠ i₀ → IsIntegral ℤ (θ i))
    (hsum : ∑ i, a i = 0) : False := by
  classical
  set Θ : ℂ := ∑ i ∈ Finset.univ.erase i₀, θ i with hΘ
  have hΘint : IsIntegral ℤ Θ := by
    rw [hΘ]
    exact IsIntegral.sum _ fun i hi => hθint i (Finset.mem_erase.mp hi).1
  have hsum2 : (p : ℂ) * Θ + 1 = 0 := by
    rw [← hsum, ← Finset.sum_erase_add Finset.univ a (Finset.mem_univ i₀), ha0, hΘ,
      Finset.mul_sum]
    congr 1
    exact (Finset.sum_congr rfl fun i hi => hθ i (Finset.mem_erase.mp hi).1).symm
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hΘval : Θ = -(p : ℂ)⁻¹ := by field_simp; linear_combination hsum2
  have hcast : Θ = algebraMap ℚ ℂ (-(p : ℚ)⁻¹) := by rw [hΘval]; push_cast; ring
  have hQ : IsIntegral ℤ (-(p : ℚ)⁻¹) := by
    have h := hΘint
    rw [hcast] at h
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℂ)
      (algebraMap ℚ ℂ).injective).mp (by simpa using h)
  exact not_isIntegral_neg_inv_prime hp hQ

end FiniteSimpleGroups

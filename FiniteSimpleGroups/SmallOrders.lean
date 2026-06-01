import Mathlib
import FiniteSimpleGroups.Basic
import FiniteSimpleGroups.Adjacent.PrimeMul

/-!
# No non-cyclic finite simple group has order < 60

The smallest non-abelian finite simple group is `A_5`, with order 60. Every
non-abelian finite simple group has order at least 60.

**Equivalent statement.** If `G` is a finite simple group with `|G| < 60`, then
`|G|` is prime (and `G ≅ Z/pZ`).

**Proof sketch.** Run Sylow analysis order by order. The main techniques:

1. **Prime-power orders** (`|G| = p^k` with `k ≥ 2`). A finite `p`-group has
   non-trivial center (`IsPGroup.center_nontrivial`). In a simple group the
   center is either `⊥` or `⊤`; it can't be `⊥` (we just showed it nontrivial),
   so it's `⊤`, meaning `G` is abelian. A finite abelian simple group is cyclic
   of prime order (`IsSimpleGroup.prime_card`), forcing `k = 1`.

2. **Two-prime orders** (`|G| = p·q` with `p < q` primes). Sylow's theorems
   pin down `n_q = 1`, so the Sylow `q`-subgroup is normal. Proved in
   [`Adjacent/PrimeMul.lean`](Adjacent/PrimeMul.lean).

3. **Mixed orders** (`p^a · q`, `p · q · r`, etc.). Order-by-order Sylow
   analysis. The hardest cases under 60 are `|G| = 24, 30, 36, 48`. Standard
   textbook exercises.

This file proves the unified statement `prime_card_of_simpleGroup_card_lt_sixty`
in full, sorry-free: (1) via `not_isSimpleGroup_of_card_prime_pow_ge_two`, (2) via
`Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime`, and every mixed order via
a reusable Sylow-counting toolkit (counts forced to `1`, the faithful-action
embedding `|G| ∣ n_p!`, and element counting for `30` and `56`).

Part of the Sylow-counting infrastructure (several of the `private` toolkit
lemmas) was substantially produced by Harmonic's Aristotle auto-formalizer (the
`lt60` job), then ported v4.28.0 → v4.29.1 and assembled here; the order-30
discharge and the mixed-order + dispatch lemmas were written by hand on top of it.
-/

namespace FiniteSimpleGroups

open Fintype Subgroup MulAction Sylow

/-! ### Sylow-counting toolkit (shared by the mixed-order cases) -/

/-- A finite simple `p`-group has prime order. -/
private lemma prime_of_simple_isPGroup {G : Type*} [Group G] [Finite G] [Nontrivial G]
    [IsSimpleGroup G] {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) :
    (Nat.card G).Prime := by
  have h_center : (Subgroup.center G) = ⊤ := by
    have h_center_normal : Subgroup.Normal (Subgroup.center G) := by infer_instance
    have h_center_cases : Subgroup.center G = ⊥ ∨ Subgroup.center G = ⊤ := by grind +suggestions
    have h_center_nontrivial : Nontrivial (Subgroup.center G) := by convert IsPGroup.center_nontrivial hp
    cases h_center_nontrivial; aesop
  convert @IsSimpleGroup.prime_card G ?_ ?_
  apply_rules [Group.commGroupOfCenterEqTop]
  infer_instance

/-- If the (unique) Sylow `p`-subgroup is the only one (`n_p = 1`), it is a proper,
nontrivial, normal subgroup — impossible in a simple group that is not a `p`-group. -/
private lemma false_of_card_sylow_eq_one_of_not_isPGroup
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    {p : ℕ} [hp : Fact p.Prime]
    (h_card : Nat.card (Sylow p G) = 1)
    (h_dvd : p ∣ Nat.card G)
    (h_not_pgroup : ¬ IsPGroup p G) : False := by
  have h_subsingleton : Subsingleton (Sylow p G) := by
    rw [Nat.card_eq_one_iff_unique] at h_card; exact h_card.1
  obtain ⟨P, _⟩ : ∃ P : Sylow p G, True := by simp
  have hP_bot_or_top : (P : Subgroup G) = ⊥ ∨ (P : Subgroup G) = ⊤ := by
    apply IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G); exact?
  cases' hP_bot_or_top with h h
  · have hP_card : Nat.card (P : Subgroup G) = p ^ (Nat.card G).factorization p := by
      convert P.card_eq_multiplicity
    simp_all +decide [Nat.Prime.pow_eq_iff]
    exact absurd hP_card (ne_of_lt (one_lt_pow₀ hp.1.one_lt
      (Nat.ne_of_gt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp
        (by exact Nat.mem_primeFactors.mpr ⟨hp.1, h_dvd, Nat.card_pos.ne'⟩))))))
  · exact h_not_pgroup (by convert P.isPGroup'; simp +decide [h, IsPGroup])

/-- In a simple group, the conjugation action on the Sylow `p`-subgroups is faithful
when `n_p > 1`, embedding `G` into `Sym (Sylow p G)`; hence `|G| ∣ n_p !`. -/
private lemma card_dvd_factorial_of_card_sylow_gt_one
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    {p : ℕ} [hp : Fact p.Prime]
    (h_gt : 1 < Nat.card (Sylow p G)) :
    Nat.card G ∣ (Nat.card (Sylow p G)).factorial := by
  let φ := MulAction.toPermHom G (Sylow p G)
  have h_kernel_bot : φ.ker = ⊥ := by
    have h_ker_normal : φ.ker.Normal := by infer_instance
    have := IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker
    cases' this h_ker_normal with h h <;> simp_all +decide [Subgroup.eq_top_iff']
    have h_fix : ∀ P : Sylow p G, ∀ g : G, g • P = P := by
      intro P g; specialize h g; replace h := Equiv.Perm.ext_iff.mp h P; aesop
    have h_unique : ∀ P Q : Sylow p G, P = Q := by
      intro P Q; have := MulAction.exists_smul_eq G P Q; aesop
    exact absurd (Fintype.card_le_one_iff.mpr fun P Q => h_unique P Q) h_gt.not_ge
  convert Subgroup.card_subgroup_dvd_card (φ.range) using 1
  · exact Nat.card_congr (Equiv.ofInjective _ <| (MonoidHom.ker_eq_bot_iff _).mp h_kernel_bot)
  · exact?

/-- Sylow III, packaged: the number of Sylow `p`-subgroups divides `|G|` and is
`≡ 1 [MOD p]`. -/
private lemma sylow_card_dvd_modEq (G : Type*) [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Nat.card (Sylow p G) ∣ Nat.card G ∧ Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  refine ⟨?_, card_sylow_modEq_one p G⟩
  rw [Nat.card_congr (Sylow.equivQuotientNormalizer (Classical.arbitrary (Sylow p G)))]
  exact Subgroup.card_quotient_dvd_card _

/-- Two finite subgroups of coprime orders intersect trivially. -/
private lemma card_coprime_inf_eq_bot {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hc : Nat.Coprime (Nat.card H) (Nat.card K)) :
    H ⊓ K = ⊥ := by
  rw [Subgroup.eq_bot_iff_card]
  exact Nat.eq_one_of_dvd_coprimes hc
    (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right)

/-- Two distinct Sylow `p`-subgroups of prime order `p` intersect trivially. -/
private lemma sylow_prime_inf_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact p.Prime]
    (hv : (Nat.card G).factorization p = 1)
    (P Q : Sylow p G) (hne : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  have hPQ_card : Nat.card (↥(P.toSubgroup ⊓ Q.toSubgroup)) ∣ p := by
    have hP_card : Nat.card P = p := by
      rw [ Sylow.card_eq_multiplicity ] ; simp +decide [ hv ];
    convert Subgroup.card_dvd_of_le ( inf_le_left : ( P.toSubgroup ⊓ Q.toSubgroup : Subgroup G ) ≤ P.toSubgroup ) using 1;
    exact hP_card.symm;
  rw [ Nat.dvd_prime hp.1 ] at hPQ_card;
  cases' hPQ_card with h h;
  · rw [ Subgroup.eq_bot_iff_card ] ; aesop;
  · have hPQ_eq_P : (P.toSubgroup ⊓ Q.toSubgroup) = P.toSubgroup := by
      have hPQ_eq_P : Nat.card (↥(P.toSubgroup ⊓ Q.toSubgroup)) = Nat.card (↥P.toSubgroup) := by
        have := P.card_eq_multiplicity; aesop;
      contrapose! hPQ_eq_P;
      refine' ne_of_lt ( Set.ncard_lt_ncard _ _ );
      · simp_all +decide [ Set.ssubset_def, Set.subset_def ];
        exact Set.not_subset.mp hPQ_eq_P;
      · exact Set.toFinite _
    have hPQ_eq_Q : (P.toSubgroup ⊓ Q.toSubgroup) = Q.toSubgroup := by
      have hPQ_eq_Q : Nat.card (↥(P.toSubgroup ⊓ Q.toSubgroup)) = Nat.card (↥(Q.toSubgroup)) := by
        have := Sylow.card_eq_multiplicity Q; aesop;
      contrapose! hPQ_eq_Q;
      refine' ne_of_lt ( Set.ncard_lt_ncard _ _ );
      · simp +zetaDelta at *;
        exact hPQ_eq_Q;
      · exact Set.toFinite _
    have hP_eq_Q : P = Q := by
      grind +suggestions
    contradiction

/-- The count of non-identity elements lying in some Sylow `p`-subgroup, when those
subgroups have prime order `p`: it equals `n_p · (p - 1)` (they pairwise meet at `1`). -/
private lemma card_nonidentity_in_prime_sylow_union {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hv : (Nat.card G).factorization p = 1) :
    Nat.card {g : G | g ≠ 1 ∧ ∃ Q : Sylow p G, g ∈ (Q : Subgroup G)} =
    Nat.card (Sylow p G) * (p - 1) := by
  rw [ ← Nat.card_congr ];
  any_goals exact ( Σ Q : Sylow p G, { g : ↥ ( Q : Subgroup G ) // g.1 ≠ 1 } );
  · have h_card : ∀ Q : Sylow p G, Nat.card {g : (Q : Subgroup G) // g.1 ≠ 1} = p - 1 := by
      intro Q
      have h_card_Q : Nat.card (Q : Subgroup G) = p := by
        have := Sylow.card_eq_multiplicity Q; aesop;
      have h_card_nonid : Nat.card {g : (Q : Subgroup G) // g.1 ≠ 1} = Nat.card (Q : Subgroup G) - 1 := by
        convert Set.ncard_diff _ _;
        any_goals exact { 1 };
        · fapply Set.ncard_congr;
          use fun a ha => a.val;
          · aesop;
          · aesop;
          · exact fun b hb => ⟨ ⟨ b, hb.1 ⟩, hb.2, rfl ⟩;
        · simp +decide [ Set.ncard_eq_toFinset_card' ];
        · exact Set.singleton_subset_iff.mpr ( Q.1.one_mem );
        · exact Set.finite_singleton 1
      rw [h_card_nonid, h_card_Q];
    simp +decide only [Nat.card_sigma, h_card];
    simp +decide [ ← mul_tsub ];
  · refine' Equiv.ofBijective ( fun x => ⟨ x.2.1, x.2.2, x.1, x.2.1.2 ⟩ ) ⟨ fun x y h => _, fun x => _ ⟩;
    · have h_eq : (x.1 : Subgroup G) ⊓ (y.1 : Subgroup G) = ⊥ ∨ x.1 = y.1 := by
        exact Classical.or_iff_not_imp_right.2 fun hxy => sylow_prime_inf_eq_bot hv x.1 y.1 hxy;
      cases h_eq <;> simp_all +decide [ Subgroup.eq_bot_iff_forall ];
      · grind;
      · aesop;
    · aesop

/-! ### Order 56 (`2³ · 7`) -/

private lemma sylow_7_options_56 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 56) :
    Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
  have h_sylow_7_div : Nat.card (Sylow 7 G) ∣ 56 ∧ Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := by
    constructor;
    · rw [ ← h ];
      haveI := Fact.mk ( show Nat.Prime 7 by decide );
      rw [ Nat.card_congr ( Sylow.equivQuotientNormalizer ( Classical.arbitrary ( Sylow 7 G ) ) ) ];
      exact Subgroup.card_quotient_dvd_card _;
    · convert card_sylow_modEq_one 7 G using 1;
      decide +kernel;
  have := Nat.le_of_dvd ( by decide ) h_sylow_7_div.1; interval_cases Nat.card ( Sylow 7 G ) <;> trivial;

private lemma sylow_2_options_56 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 56) :
    Nat.card (Sylow 2 G) = 1 ∨ Nat.card (Sylow 2 G) = 7 := by
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 G, True := by
    simp +zetaDelta at *;
  have h_index : P.1.index = 7 := by
    have := Subgroup.index_mul_card P.toSubgroup;
    have h_card_P : Nat.card (P : Subgroup G) = 8 := by
      convert P.card_eq_multiplicity;
      rw [ h ] ; native_decide;
    grind;
  have h_div : Nat.card (Sylow 2 G) ∣ 7 := by
    convert P.card_dvd_index;
    exact h_index.symm;
  rwa [ Nat.dvd_prime ( by decide ) ] at h_div

private lemma sylow_2_unique_of_8_sylow_7 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 56)
    (h7 : Nat.card (Sylow 7 G) = 8) :
    Nat.card (Sylow 2 G) = 1 := by
  set R := {g : G | g ≠ 1 ∧ ¬∃ Q : Sylow 7 G, g ∈ (Q : Subgroup G)} with hR_def
  have hR_card : Nat.card R = 7 := by
    have h_card_S7 : Nat.card {g : G | g ≠ 1 ∧ ∃ Q : Sylow 7 G, g ∈ (Q : Subgroup G)} = 8 * (7 - 1) := by
      convert card_nonidentity_in_prime_sylow_union _;
      · exact h7.symm;
      · infer_instance;
      · native_decide +revert;
      · exact h.symm ▸ by native_decide;
    have h_card_R : Nat.card R = Nat.card {g : G | g ≠ 1} - Nat.card {g : G | g ≠ 1 ∧ ∃ Q : Sylow 7 G, g ∈ (Q : Subgroup G)} := by
      rw [ tsub_eq_of_eq_add ];
      simp +decide [ Set.setOf_and, Set.setOf_or ];
      rw [ ← @Set.ncard_union_eq ];
      · congr with x ; by_cases hx : ∃ Q : Sylow 7 G, x ∈ ( Q : Subgroup G ) <;> aesop;
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₁.2 hx₂.2;
      · exact Set.toFinite R;
      · exact Set.toFinite _;
    have h_card_G : Nat.card {g : G | g ≠ 1} = Nat.card G - 1 := by
      have : {g : G | g ≠ 1} = Set.univ \ {1} := by
        grind +splitIndPred
      simp +decide [ this, Set.toFinset_card ];
    grind +revert;
  have hP_subset_R : ∀ P : Sylow 2 G, {g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} ⊆ R := by
    intro P g hg
    obtain ⟨hgP, hg_ne⟩ := hg
    have h_inter : ∀ Q : Sylow 7 G, (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
      intro Q
      have h_inter : Nat.card (P : Subgroup G) = 8 ∧ Nat.card (Q : Subgroup G) = 7 := by
        haveI := Fact.mk ( by decide : Nat.Prime 2 ) ; haveI := Fact.mk ( by decide : Nat.Prime 7 ) ; have := Sylow.card_eq_multiplicity P; have := Sylow.card_eq_multiplicity Q; simp_all +decide ;
        native_decide +revert;
      have := card_coprime_inf_eq_bot ( P : Subgroup G ) ( Q : Subgroup G ) ?_ <;> simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ];
    simp_all +decide [ SetLike.ext_iff ];
    grind +extAll;
  have hP_card : ∀ P : Sylow 2 G, Nat.card {g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} = 7 := by
    intro P
    have hP_card : Nat.card (P : Subgroup G) = 8 := by
      convert P.card_eq_multiplicity using 1 ; norm_num [ h ];
      native_decide;
    convert Nat.card_congr ( Equiv.subtypeEquivRight ( show ∀ g : G, g ∈ ( P : Subgroup G ) ∧ ¬g = 1 ↔ g ∈ ( P : Subgroup G ) ∧ g ≠ 1 from fun g => Iff.rfl ) ) using 1;
    convert congr_arg ( fun x : ℕ => x - 1 ) hP_card.symm using 1;
    convert Set.ncard_diff_singleton_of_mem ( show 1 ∈ ( P : Subgroup G ) from P.1.one_mem ) using 1;
  have hP_eq_R : ∀ P : Sylow 2 G, {g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} = R := by
    intro P
    apply Set.eq_of_subset_of_ncard_le
    exact hP_subset_R P
    have hP_card_eq : Nat.card {g : G | g ∈ (P : Subgroup G) ∧ g ≠ 1} = Nat.card R := by
      rw [ hP_card P, hR_card ]
    exact hP_card_eq.ge;
    exact Set.toFinite R;
  have hP_eq_P2 : ∀ P₁ P₂ : Sylow 2 G, (P₁ : Subgroup G) = (P₂ : Subgroup G) := by
    intro P₁ P₂; ext g; by_cases hg : g = 1 <;> simp_all +decide [ Set.ext_iff ] ;
    grind +ring;
  convert Nat.card_eq_one_iff_unique.mpr _;
  exact ⟨ ⟨ fun P₁ P₂ => Sylow.ext ( hP_eq_P2 P₁ P₂ ) ⟩, ⟨ Classical.arbitrary _ ⟩ ⟩

/-- There is no finite simple group of order 56. -/
private lemma no_simple_group_order_56
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 56) : False := by
  rcases sylow_7_options_56 h with h7 | h7
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact false_of_card_sylow_eq_one_of_not_isPGroup h7
      (by rw [h]; norm_num)
      (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))
  · have h2 := sylow_2_unique_of_8_sylow_7 h h7
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact false_of_card_sylow_eq_one_of_not_isPGroup h2
      (by rw [h]; norm_num)
      (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

/-! ### Order 30 (`2 · 3 · 5`) -/

private lemma sylow_5_options_30 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 30) :
    Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 := by
  haveI := Fact.mk (show Nat.Prime 5 by decide)
  have h_div : Nat.card (Sylow 5 G) ∣ 30 ∧ Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := by
    constructor
    · rw [← h]
      rw [Nat.card_congr (Sylow.equivQuotientNormalizer (Classical.arbitrary (Sylow 5 G)))]
      exact Subgroup.card_quotient_dvd_card _
    · convert card_sylow_modEq_one 5 G using 1
  have := Nat.le_of_dvd (by decide) h_div.1
  interval_cases Nat.card (Sylow 5 G) <;> trivial

private lemma sylow_3_options_30 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 30) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 10 := by
  haveI := Fact.mk (show Nat.Prime 3 by decide)
  have h_div : Nat.card (Sylow 3 G) ∣ 30 ∧ Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := by
    constructor
    · rw [← h]
      rw [Nat.card_congr (Sylow.equivQuotientNormalizer (Classical.arbitrary (Sylow 3 G)))]
      exact Subgroup.card_quotient_dvd_card _
    · convert card_sylow_modEq_one 3 G using 1
  have := Nat.le_of_dvd (by decide) h_div.1
  interval_cases Nat.card (Sylow 3 G) <;> trivial

/-- There is no finite simple group of order 30. -/
private lemma no_simple_group_order_30
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 30) : False := by
  haveI hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hp3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rcases sylow_5_options_30 h with h5 | h5
  · exact false_of_card_sylow_eq_one_of_not_isPGroup h5 (by rw [h]; norm_num)
      (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))
  rcases sylow_3_options_30 h with h3 | h3
  · exact false_of_card_sylow_eq_one_of_not_isPGroup h3 (by rw [h]; norm_num)
      (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))
  -- Otherwise n₅ = 6 and n₃ = 10. Element counting: the Sylow 5- and Sylow 3-subgroups
  -- contribute 6·4 = 24 and 10·2 = 20 distinct non-identity elements respectively; these
  -- are disjoint and all lie among the 29 non-identity elements of G. 24 + 20 = 44 > 29.
  have hv5 : (Nat.card G).factorization 5 = 1 := by rw [h]; native_decide
  have hv3 : (Nat.card G).factorization 3 = 1 := by rw [h]; native_decide
  set A := {g : G | g ≠ 1 ∧ ∃ Q : Sylow 5 G, g ∈ (Q : Subgroup G)} with hA
  set B := {g : G | g ≠ 1 ∧ ∃ Q : Sylow 3 G, g ∈ (Q : Subgroup G)} with hB
  have hS5 : A.ncard = 24 := by
    show Nat.card A = 24
    have key := card_nonidentity_in_prime_sylow_union (G := G) hv5
    rw [h5] at key
    exact key
  have hS3 : B.ncard = 20 := by
    show Nat.card B = 20
    have key := card_nonidentity_in_prime_sylow_union (G := G) hv3
    rw [h3] at key
    exact key
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro g hgA hgB
    rw [hA, Set.mem_setOf_eq] at hgA
    rw [hB, Set.mem_setOf_eq] at hgB
    obtain ⟨hg_ne, P5, hgP5⟩ := hgA
    obtain ⟨-, P3, hgP3⟩ := hgB
    have hbot : (P5 : Subgroup G) ⊓ (P3 : Subgroup G) = ⊥ := by
      apply card_coprime_inf_eq_bot
      have hc5 : Nat.card (P5 : Subgroup G) = 5 := by
        rw [Sylow.card_eq_multiplicity, hv5]; norm_num
      have hc3 : Nat.card (P3 : Subgroup G) = 3 := by
        rw [Sylow.card_eq_multiplicity, hv3]; norm_num
      rw [hc5, hc3]; decide
    have hg_bot : g ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_inf.mpr ⟨hgP5, hgP3⟩
    exact hg_ne (Subgroup.mem_bot.mp hg_bot)
  have h_ne1 : {g : G | g ≠ 1}.ncard = 29 := by
    have heq : {g : G | g ≠ 1} = (Set.univ : Set G) \ {1} := by ext g; simp
    rw [heq, Set.ncard_diff (Set.singleton_subset_iff.mpr (Set.mem_univ _)) (Set.toFinite _),
      Set.ncard_univ, Set.ncard_singleton, h]
  have h_union_le : (A ∪ B).ncard ≤ {g : G | g ≠ 1}.ncard :=
    Set.ncard_le_ncard (Set.union_subset (fun _ hx => hx.1) (fun _ hx => hx.1)) (Set.toFinite _)
  have h_union_eq : (A ∪ B).ncard = 24 + 20 := by
    rw [Set.ncard_union_eq h_disj (Set.toFinite _) (Set.toFinite _), hS5, hS3]
  omega

/-! ### Mixed orders: a Sylow count is forced to 1 (proper normal Sylow subgroup)

For these orders there is a prime `p` for which the only value of `n_p` compatible
with `n_p ∣ |G|` and `n_p ≡ 1 [MOD p]` is `1` — so the Sylow `p`-subgroup is normal,
contradicting simplicity. (`omega` discharges the divisibility+congruence arithmetic.) -/

private lemma no_simple_group_order_18
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 18) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 3)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 3 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 3 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_20
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 20) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 5)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 5 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 5 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_28
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 28) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 7)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 7 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 7 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_40
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 40) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 5)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 5 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 5 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_42
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 42) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 7)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 7 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 7 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_44
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 44) : False := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 11)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 11 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 11 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_45
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 45) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 5)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 5 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 5 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_50
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 50) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 5)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 5 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 5 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_52
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 52) : False := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 13)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 13 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 13 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_54
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 54) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 3)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 3 G) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases (Nat.card (Sylow 3 G)) <;> omega
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

/-! ### Mixed orders: the faithful action on Sylow subgroups embeds `G` (`|G| ∣ n_p!`)

Here `n_p ∈ {1, k}` with `k > 1`, but `k` is killed by `|G| ∣ k!` being false (the
conjugation action on the `k` Sylow `p`-subgroups is faithful in a simple group), so
`n_p = 1` and the Sylow `p`-subgroup is normal. -/

private lemma no_simple_group_order_12
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 12) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 2)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 2 G) = 1 := by
    by_contra h1
    have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
    have hgt : 1 < Nat.card (Sylow 2 G) := lt_of_le_of_ne hpos (Ne.symm h1)
    have hemb := card_dvd_factorial_of_card_sylow_gt_one hgt
    rw [h] at hemb
    have hk : Nat.card (Sylow 2 G) = 3 := by
      have hle := Nat.le_of_dvd (by norm_num) hd
      interval_cases (Nat.card (Sylow 2 G)) <;> omega
    rw [hk] at hemb
    exact absurd hemb (by decide)
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_24
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 24) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 2)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 2 G) = 1 := by
    by_contra h1
    have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
    have hgt : 1 < Nat.card (Sylow 2 G) := lt_of_le_of_ne hpos (Ne.symm h1)
    have hemb := card_dvd_factorial_of_card_sylow_gt_one hgt
    rw [h] at hemb
    have hk : Nat.card (Sylow 2 G) = 3 := by
      have hle := Nat.le_of_dvd (by norm_num) hd
      interval_cases (Nat.card (Sylow 2 G)) <;> omega
    rw [hk] at hemb
    exact absurd hemb (by decide)
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_36
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 36) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 3)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 3 G) = 1 := by
    by_contra h1
    have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
    have hgt : 1 < Nat.card (Sylow 3 G) := lt_of_le_of_ne hpos (Ne.symm h1)
    have hemb := card_dvd_factorial_of_card_sylow_gt_one hgt
    rw [h] at hemb
    have hk : Nat.card (Sylow 3 G) = 4 := by
      have hle := Nat.le_of_dvd (by norm_num) hd
      interval_cases (Nat.card (Sylow 3 G)) <;> omega
    rw [hk] at hemb
    exact absurd hemb (by decide)
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

private lemma no_simple_group_order_48
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 48) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨hd, hm⟩ := sylow_card_dvd_modEq G (p := 2)
  rw [h] at hd
  simp only [Nat.ModEq] at hm
  have h1 : Nat.card (Sylow 2 G) = 1 := by
    by_contra h1
    have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
    have hgt : 1 < Nat.card (Sylow 2 G) := lt_of_le_of_ne hpos (Ne.symm h1)
    have hemb := card_dvd_factorial_of_card_sylow_gt_one hgt
    rw [h] at hemb
    have hk : Nat.card (Sylow 2 G) = 3 := by
      have hle := Nat.le_of_dvd (by norm_num) hd
      interval_cases (Nat.card (Sylow 2 G)) <;> omega
    rw [hk] at hemb
    exact absurd hemb (by decide)
  exact false_of_card_sylow_eq_one_of_not_isPGroup h1 (by rw [h]; norm_num)
    (fun hp => absurd (h ▸ prime_of_simple_isPGroup hp) (by norm_num))

/-! ### Prime-power case -/

/-- Any group of prime-power order `p^k` with `k ≥ 2` has a non-trivial center,
hence is not simple. The center is a normal subgroup; in a simple group it
would have to be `⊥` or `⊤`; the `p`-group center theorem rules out `⊥`; and
`⊤` would make `G` abelian, forcing `|G|` to be prime (so `k = 1`). -/
theorem not_isSimpleGroup_of_card_prime_pow_ge_two
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (h_card : Nat.card G = p ^ k) :
    ¬ IsSimpleGroup G := by
  intro h_simple
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (Subgroup.center G) := (IsPGroup.of_card h_card).center_nontrivial
  rcases h_simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with
    h_bot | h_top
  · have h_sub : Subsingleton ↥(Subgroup.center G) := by
      rw [h_bot]
      refine ⟨fun a b => Subtype.ext ?_⟩
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2]
    exact (not_subsingleton_iff_nontrivial.mpr inferInstance) h_sub
  · let _ : CommGroup G := Group.commGroupOfCenterEqTop h_top
    have h_pcard : (Nat.card G).Prime := IsSimpleGroup.prime_card
    rw [h_card] at h_pcard
    have h_factor : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
    have h_p_eq_pk : p = p ^ k :=
      h_pcard.eq_one_or_self_of_dvd p h_factor |>.resolve_left hp.one_lt.ne'
    have : p ^ 1 = p ^ k := by simpa using h_p_eq_pk
    have hk_eq : 1 = k := Nat.pow_right_injective hp.two_le this
    omega

/-! ### One concrete mixed-order case (use `Adjacent.PrimeMul` for general `p·q`) -/

/-- No group of order 6 is simple. (Both `Z/6` and `S_3` exist; neither is simple.) -/
theorem not_isSimpleGroup_of_card_six
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (h_card : Nat.card G = 6) : ¬ IsSimpleGroup G := by
  apply Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime
    Nat.prime_two Nat.prime_three (by omega : 2 < 3)
  rw [h_card]

/-! ### Uniform `False`-returning wrappers for every composite order < 60

So the main theorem's `interval_cases` dispatch is uniform: each composite order
`k` gets `no_simple_group_order_k : Nat.card G = k → False`. Prime powers delegate
to `not_isSimpleGroup_of_card_prime_pow_ge_two`; products of two distinct primes to
`Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime`; the mixed orders use the
Sylow-counting lemmas above. -/

-- Prime powers p^k, k ≥ 2.
private lemma no_simple_group_order_4 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 4) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 2) (k := 2) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_8 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 8) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 2) (k := 3) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_9 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 9) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 3) (k := 2) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_16 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 16) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 2) (k := 4) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_25 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 25) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 5) (k := 2) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_27 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 27) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 3) (k := 3) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_32 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 32) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 2) (k := 5) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_49 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 49) : False :=
  not_isSimpleGroup_of_card_prime_pow_ge_two (p := 7) (k := 2) (by norm_num) (by norm_num)
    (h.trans (by norm_num)) ‹IsSimpleGroup G›

-- Products of two distinct primes p·q.
private lemma no_simple_group_order_6 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 6) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 3)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_10 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 10) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 5)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_14 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 14) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_15 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 15) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 3) (q := 5)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_21 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 21) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 3) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_22 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 22) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 11)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_26 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 26) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 13)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_33 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 33) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 3) (q := 11)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_34 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 34) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 17)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_35 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 35) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 5) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_38 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 38) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 19)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_39 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 39) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 3) (q := 13)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_46 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 46) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 23)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_51 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 51) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 3) (q := 17)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_55 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 55) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 5) (q := 11)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_57 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 57) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 3) (q := 19)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›
private lemma no_simple_group_order_58 {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h : Nat.card G = 58) : False :=
  Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime (p := 2) (q := 29)
    (by norm_num) (by norm_num) (by norm_num) (h.trans (by norm_num)) ‹IsSimpleGroup G›

/-! ### Main theorem

The unified statement is proved by order-by-order Sylow analysis. Every composite
order `< 60` is dispatched to a `no_simple_group_order_k : Nat.card G = k → False`:
* Prime powers (4, 8, 9, 16, 25, 27, 32, 49) → `not_isSimpleGroup_of_card_prime_pow_ge_two`.
* Products of two distinct primes (6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38,
  39, 46, 51, 55, 57, 58) → `Adjacent.not_isSimpleGroup_of_card_eq_prime_mul_prime`.
* Mixed orders: a Sylow count forced to `1` (18, 20, 28, 40, 42, 44, 45, 50, 52,
  54), the faithful-action embedding `|G| ∣ n_p!` (12, 24, 36, 48), or element
  counting (30, 56). -/

/-- **The main result.** Every finite simple group of order less than 60 has
prime order (hence is cyclic) — equivalently, the smallest non-abelian finite
simple group, `A₅`, has order 60. Proved sorry-free by `interval_cases` over
`2 ≤ |G| < 60`, dispatching each composite order to its Sylow argument. -/
theorem prime_card_of_simpleGroup_card_lt_sixty
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h_lt : Nat.card G < 60) : (Nat.card G).Prime := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card G = n := ⟨_, rfl⟩
  have h2 : 2 ≤ n := by rw [← hn]; exact Finite.one_lt_card
  rw [hn] at h_lt
  interval_cases n <;>
    first
      | exact (no_simple_group_order_4 hn).elim
      | exact (no_simple_group_order_6 hn).elim
      | exact (no_simple_group_order_8 hn).elim
      | exact (no_simple_group_order_9 hn).elim
      | exact (no_simple_group_order_10 hn).elim
      | exact (no_simple_group_order_12 hn).elim
      | exact (no_simple_group_order_14 hn).elim
      | exact (no_simple_group_order_15 hn).elim
      | exact (no_simple_group_order_16 hn).elim
      | exact (no_simple_group_order_18 hn).elim
      | exact (no_simple_group_order_20 hn).elim
      | exact (no_simple_group_order_21 hn).elim
      | exact (no_simple_group_order_22 hn).elim
      | exact (no_simple_group_order_24 hn).elim
      | exact (no_simple_group_order_25 hn).elim
      | exact (no_simple_group_order_26 hn).elim
      | exact (no_simple_group_order_27 hn).elim
      | exact (no_simple_group_order_28 hn).elim
      | exact (no_simple_group_order_30 hn).elim
      | exact (no_simple_group_order_32 hn).elim
      | exact (no_simple_group_order_33 hn).elim
      | exact (no_simple_group_order_34 hn).elim
      | exact (no_simple_group_order_35 hn).elim
      | exact (no_simple_group_order_36 hn).elim
      | exact (no_simple_group_order_38 hn).elim
      | exact (no_simple_group_order_39 hn).elim
      | exact (no_simple_group_order_40 hn).elim
      | exact (no_simple_group_order_42 hn).elim
      | exact (no_simple_group_order_44 hn).elim
      | exact (no_simple_group_order_45 hn).elim
      | exact (no_simple_group_order_46 hn).elim
      | exact (no_simple_group_order_48 hn).elim
      | exact (no_simple_group_order_49 hn).elim
      | exact (no_simple_group_order_50 hn).elim
      | exact (no_simple_group_order_51 hn).elim
      | exact (no_simple_group_order_52 hn).elim
      | exact (no_simple_group_order_54 hn).elim
      | exact (no_simple_group_order_55 hn).elim
      | exact (no_simple_group_order_56 hn).elim
      | exact (no_simple_group_order_57 hn).elim
      | exact (no_simple_group_order_58 hn).elim
      | (rw [hn]; norm_num)

end FiniteSimpleGroups


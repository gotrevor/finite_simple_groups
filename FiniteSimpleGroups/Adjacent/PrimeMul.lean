import Mathlib
import FiniteSimpleGroups.Basic

/-!
# Groups of order p·q are not simple

A CFSG-adjacent miniature: for distinct primes `p < q`, any group of order `p·q`
has a normal Sylow `q`-subgroup, hence is not simple.

**The Sylow argument.** Let `n_q` denote the number of Sylow `q`-subgroups in `G`.
By Sylow's theorems:
1. `n_q ≡ 1 (mod q)`              [Sylow III, `card_sylow_modEq_one`]
2. `n_q ∣ |G| / q = p`            [`Sylow.card_dvd_index`]

So `n_q ∈ {1, p}` and `n_q ≡ 1 (mod q)`. Since `p < q`, we have `1 ≤ p < q`, so
`p mod q = p ≠ 1` (as `p` is prime, `p ≥ 2`). Therefore `n_q = 1`, the unique
Sylow `q`-subgroup is normal, and `G` is not simple.

**Wider classification (the Harper-Wu style result).** A group of order `p·q` is
isomorphic to one of:
- `Z/pq` (cyclic, abelian), always
- A non-abelian semidirect product `Z/q ⋊ Z/p`, only when `p ∣ q - 1`

This file proves both the non-simplicity result and the cyclic-or-`p ∣ q-1`
dichotomy with real Sylow-based proofs. (The finer semidirect-product
*construction* and isomorphism-class count are not formalized here — only the
dichotomy itself, which needs pure Sylow counting, no Schur–Zassenhaus.)
-/

namespace FiniteSimpleGroups
namespace Adjacent

variable {G : Type*} [Group G]

/-- **Main non-simplicity lemma.** Any group of order `p·q` for distinct primes
`p < q` has a normal Sylow `q`-subgroup, and hence is not simple. -/
theorem not_isSimpleGroup_of_card_eq_prime_mul_prime
    [Finite G] [Nontrivial G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (h_card : Nat.card G = p * q) :
    ¬ IsSimpleGroup G := by
  intro h_simple
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- Pick any Sylow q-subgroup.
  obtain ⟨P⟩ : Nonempty (Sylow q G) := inferInstance
  -- q ∤ p (since q > p ≥ 2 and p is prime).
  have h_q_ndvd_p : ¬ q ∣ p := fun h => by
    have hqp : q ≤ p := Nat.le_of_dvd hp.pos h
    omega
  -- |P| = q (since q divides |G| = p*q exactly once).
  have h_cardP : Nat.card (P : Subgroup G) = q := by
    rw [P.card_eq_multiplicity, h_card,
        Nat.factorization_mul hp.ne_zero hq.ne_zero]
    simp [Nat.Prime.factorization_self hq,
          Nat.factorization_eq_zero_of_not_dvd h_q_ndvd_p]
  -- The index of P in G is p (since |G| / |P| = pq / q = p).
  have h_indexP : (P : Subgroup G).index = p := by
    have h_idx : (P : Subgroup G).index * Nat.card (P : Subgroup G) = Nat.card G :=
      Subgroup.index_mul_card _
    rw [h_cardP, h_card] at h_idx
    exact Nat.eq_of_mul_eq_mul_right hq.pos h_idx
  -- Sylow's theorems pin down the count of Sylow q-subgroups to 1.
  have h_count : Nat.card (Sylow q G) = 1 := by
    have h_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
    have h_dvd : Nat.card (Sylow q G) ∣ p := by
      have := P.card_dvd_index
      rwa [h_indexP] at this
    -- n_q ∈ {1, p} by primality of p; n_q ≡ 1 (mod q); p < q rules out n_q = p.
    rcases (Nat.dvd_prime hp).mp h_dvd with h_eq_1 | h_eq_p
    · exact h_eq_1
    · exfalso
      rw [h_eq_p] at h_mod
      -- p ≡ 1 (mod q) with p < q forces p = 1, contradicting p prime.
      have h_qpos : 0 < q := hq.pos
      have h_pmod : p % q = p := Nat.mod_eq_of_lt hpq
      have h_1mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
      unfold Nat.ModEq at h_mod
      rw [h_pmod, h_1mod] at h_mod
      exact hp.one_lt.ne' h_mod
  -- A unique Sylow q-subgroup is normal.
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp h_count).1
  have h_normal : (P : Subgroup G).Normal := P.normal_of_subsingleton
  -- P is a proper non-trivial normal subgroup, contradicting simplicity.
  rcases h_simple.eq_bot_or_eq_top_of_normal _ h_normal with h_bot | h_top
  · -- P = ⊥ would force |P| = 1, but |P| = q ≥ 2.
    have : Nat.card (P : Subgroup G) = 1 := by rw [h_bot]; simp
    rw [h_cardP] at this
    exact hq.one_lt.ne' this
  · -- P = ⊤ would force |P| = p·q, but |P| = q ≠ p·q (since p ≥ 2).
    have : Nat.card (P : Subgroup G) = Nat.card G := by
      rw [h_top]; exact Subgroup.card_top
    rw [h_cardP, h_card] at this
    -- this : q = p * q
    nlinarith [hp.two_le, hq.pos]

/-! ### The Harper-Wu-style structural dichotomy

For distinct primes `p < q`:

* If `¬ (p ∣ q - 1)`: the only group of order `p·q` (up to iso) is the cyclic
  group `Z/pq`. The Sylow p-subgroup is also normal (by symmetry of the same
  argument), so `G ≅ Z/p × Z/q ≅ Z/pq`.
* If `p ∣ q - 1`: there are exactly two isomorphism classes:
  - The cyclic group `Z/pq`.
  - A non-abelian semidirect product `Z/q ⋊ Z/p` (which exists precisely because
    `Aut(Z/q) ≅ (Z/q)^× ≅ Z/(q-1)` has an element of order `p`).

Neither is simple in either case (Sylow q-subgroup is always normal).

The *dichotomy* `IsCyclic G ∨ p ∣ q - 1` is proved below by pure Sylow counting;
only the explicit semidirect-product construction and isomorphism-class count
are omitted. -/

/-- **Harper-Wu dichotomy.** Any group of order `p·q` with `p < q` distinct
primes is either cyclic, or `p ∣ q - 1` (the arithmetic condition under which the
non-abelian semidirect product `Z/q ⋊ Z/p` also exists).

The proof is pure Sylow counting — **no Schur–Zassenhaus is needed for the
dichotomy.** The Sylow `q`-subgroup is always normal (`n_q = 1`, as in
`not_isSimpleGroup_of_card_eq_prime_mul_prime`). For the Sylow `p`-count,
`n_p ≡ 1 (mod p)` together with `n_p ∣ q` forces `n_p ∈ {1, q}`:

* `n_p = q` gives `q ≡ 1 (mod p)`, i.e. `p ∣ q - 1` (right branch);
* `n_p = 1` makes the Sylow `p`-subgroup normal too. Two normal subgroups of
  coprime prime orders are disjoint, hence commute elementwise; the product of
  their generators then has order `p · q = |G|`, so `G` is cyclic (left branch). -/
theorem card_eq_prime_mul_prime_classification
    [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (h_card : Nat.card G = p * q) :
    IsCyclic G ∨ (p ∣ q - 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have h_cop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq_ne
  have h_q_ndvd_p : ¬ q ∣ p := fun h => by
    have := Nat.le_of_dvd hp.pos h; omega
  have h_p_ndvd_q : ¬ p ∣ q := fun h => by
    rcases hq.eq_one_or_self_of_dvd p h with h1 | h2
    · exact hp.one_lt.ne' h1
    · omega
  -- The two Sylow subgroups, with their orders.
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  have h_cardP : Nat.card (P : Subgroup G) = p := by
    rw [P.card_eq_multiplicity, h_card, Nat.factorization_mul hp.ne_zero hq.ne_zero]
    simp [Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd h_p_ndvd_q]
  have h_cardQ : Nat.card (Q : Subgroup G) = q := by
    rw [Q.card_eq_multiplicity, h_card, Nat.factorization_mul hp.ne_zero hq.ne_zero]
    simp [Nat.Prime.factorization_self hq, Nat.factorization_eq_zero_of_not_dvd h_q_ndvd_p]
  -- Indices: |G|/|P| = q and |G|/|Q| = p.
  have h_indexP : (P : Subgroup G).index = q := by
    have h := Subgroup.index_mul_card (P : Subgroup G)
    rw [h_cardP, h_card] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h]; ring)
  have h_indexQ : (Q : Subgroup G).index = p := by
    have h := Subgroup.index_mul_card (Q : Subgroup G)
    rw [h_cardQ, h_card] at h
    exact Nat.eq_of_mul_eq_mul_right hq.pos h
  -- The Sylow q-subgroup is normal (n_q = 1).
  have h_countQ : Nat.card (Sylow q G) = 1 := by
    have h_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
    have h_dvd : Nat.card (Sylow q G) ∣ p := by
      have := Q.card_dvd_index; rwa [h_indexQ] at this
    rcases (Nat.dvd_prime hp).mp h_dvd with h1 | hpp
    · exact h1
    · exfalso
      rw [hpp, Nat.ModEq, Nat.mod_eq_of_lt hpq, Nat.mod_eq_of_lt hq.one_lt] at h_mod
      exact hp.one_lt.ne' h_mod
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp h_countQ).1
  have hQnormal : (Q : Subgroup G).Normal := Q.normal_of_subsingleton
  -- The Sylow p-count: n_p ≡ 1 (mod p) and n_p ∣ q, so n_p ∈ {1, q}.
  have h_modP : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have h_dvdP : Nat.card (Sylow p G) ∣ q := by
    have := P.card_dvd_index; rwa [h_indexP] at this
  rcases (Nat.dvd_prime hq).mp h_dvdP with h_np1 | h_npq
  · -- n_p = 1: the Sylow p-subgroup is normal too, and G is cyclic.
    left
    haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp h_np1).1
    have hPnormal : (P : Subgroup G).Normal := P.normal_of_subsingleton
    -- P and Q are disjoint: a common element has order dividing both p and q.
    have hdisj : Disjoint (P : Subgroup G) (Q : Subgroup G) := by
      rw [Subgroup.disjoint_def]
      intro x hxP hxQ
      have hdp : orderOf x ∣ p := by
        have h := orderOf_dvd_natCard (⟨x, hxP⟩ : (P : Subgroup G))
        rw [← Subgroup.orderOf_coe (⟨x, hxP⟩ : (P : Subgroup G)), h_cardP] at h
        exact h
      have hdq : orderOf x ∣ q := by
        have h := orderOf_dvd_natCard (⟨x, hxQ⟩ : (Q : Subgroup G))
        rw [← Subgroup.orderOf_coe (⟨x, hxQ⟩ : (Q : Subgroup G)), h_cardQ] at h
        exact h
      have : orderOf x = 1 := (h_cop.coprime_dvd_left hdp).eq_one_of_dvd hdq
      exact orderOf_eq_one_iff.mp this
    -- Generators of P and Q.
    haveI : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card h_cardP
    haveI : IsCyclic (Q : Subgroup G) := isCyclic_of_prime_card h_cardQ
    obtain ⟨gP, hgP⟩ := IsCyclic.exists_generator (α := ↥(P : Subgroup G))
    obtain ⟨gQ, hgQ⟩ := IsCyclic.exists_generator (α := ↥(Q : Subgroup G))
    have hoP : orderOf (gP : G) = p := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hgP, h_cardP]
    have hoQ : orderOf (gQ : G) = q := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hgQ, h_cardQ]
    -- They commute (normal + disjoint), and their orders are coprime.
    have hcomm : Commute (gP : G) (gQ : G) :=
      Subgroup.commute_of_normal_of_disjoint _ _ hPnormal hQnormal hdisj _ _ gP.2 gQ.2
    have hco : (orderOf (gP : G)).Coprime (orderOf (gQ : G)) := by
      rw [hoP, hoQ]; exact h_cop
    -- Hence the product has order p·q = |G|, so G is cyclic.
    have hord : orderOf ((gP : G) * (gQ : G)) = Nat.card G := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hoP, hoQ, h_card]
    exact isCyclic_of_orderOf_eq_card _ hord
  · -- n_p = q: then q ≡ 1 (mod p), i.e. p ∣ q - 1.
    right
    rw [h_npq] at h_modP
    exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).mp h_modP.symm

end Adjacent
end FiniteSimpleGroups

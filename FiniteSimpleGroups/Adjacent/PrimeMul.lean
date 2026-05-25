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

This file states the non-simplicity result with a real Sylow-based proof, and
the cyclic-vs-semidirect dichotomy as a high-level statement (proof relies on
Schur–Zassenhaus + a semidirect product construction; left as `sorry`).
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

Statement-only here; the construction of the semidirect product and uniqueness
arguments need more infrastructure than this scaffold provides. -/

/-- **Harper-Wu dichotomy (statement only).** Any group of order `p·q` with
`p < q` distinct primes is either cyclic, or (when `p ∣ q - 1`) the non-abelian
semidirect product `Z/q ⋊ Z/p`. -/
theorem card_eq_prime_mul_prime_classification
    [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (h_card : Nat.card G = p * q) :
    IsCyclic G ∨ (p ∣ q - 1) := by
  sorry -- Real classification: Sylow + Schur-Zassenhaus. Out of scope here.

end Adjacent
end FiniteSimpleGroups

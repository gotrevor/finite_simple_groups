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

This file proves (1) in full, cites (2) from `PrimeMul.lean`, and gives one
representative mixed-order case (`|G| = 6`) plus a structured sorry for the
unified "every simple group of order < 60 has prime order" statement.
-/

namespace FiniteSimpleGroups

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
  · -- center = ⊥ would make the center subsingleton, contradicting nontriviality.
    have h_sub : Subsingleton ↥(Subgroup.center G) := by
      rw [h_bot]
      refine ⟨fun a b => Subtype.ext ?_⟩
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2]
    exact (not_subsingleton_iff_nontrivial.mpr inferInstance) h_sub
  · -- center = ⊤ → G is commutative → finite simple commutative → prime order
    let _ : CommGroup G := Group.commGroupOfCenterEqTop h_top
    have h_pcard : (Nat.card G).Prime := IsSimpleGroup.prime_card
    rw [h_card] at h_pcard
    -- p^k prime with k ≥ 2 is impossible
    have h_factor : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
    have h_p_eq_pk : p = p ^ k :=
      h_pcard.eq_one_or_self_of_dvd p h_factor |>.resolve_left hp.one_lt.ne'
    -- p = p^k with k ≥ 2 ⇒ p^1 = p^k ⇒ 1 = k by Nat.pow_right_injective
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

/-! ### Main theorem (structured sorry)

The unified statement requires checking all orders 4, 6, 8, 9, ..., 59 that
aren't prime. Lemmas above handle:
* Prime powers (4, 8, 9, 16, 25, 27, 32, 49)
* Products of two distinct primes (6, 10, 14, 15, 21, 22, 26, 33, 34, 35, 38,
  39, 46, 51, 55, 57, 58)

Remaining cases needing individual Sylow analysis (or a unified Sylow-based
argument):
* `12 = 2² · 3`, `18 = 2 · 3²`, `20 = 2² · 5`, `24 = 2³ · 3`, `28 = 2² · 7`,
  `30 = 2 · 3 · 5`, `36 = 2² · 3²`, `40 = 2³ · 5`, `42 = 2 · 3 · 7`,
  `44 = 2² · 11`, `45 = 3² · 5`, `48 = 2⁴ · 3`, `50 = 2 · 5²`,
  `52 = 2² · 13`, `54 = 2 · 3³`, `56 = 2³ · 7`

The unified theorem is left as `sorry`; the techniques are in place. -/

/-- **The main result.** Every finite simple group of order less than 60 has
prime order (and is therefore cyclic). Proven for prime-power and two-distinct-
prime orders; mixed orders remain `sorry`. -/
theorem prime_card_of_simpleGroup_card_lt_sixty
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSimpleGroup G]
    (h_lt : Nat.card G < 60) : (Nat.card G).Prime := by
  sorry -- Order-by-order case analysis using the lemmas above for prime powers
        -- and PrimeMul.not_isSimpleGroup_of_card_eq_prime_mul_prime for pq.
        -- Mixed cases (12, 18, 20, 24, 28, 30, 36, 40, 42, 44, 45, 48, 50, 52,
        -- 54, 56) need additional Sylow arguments.

end FiniteSimpleGroups

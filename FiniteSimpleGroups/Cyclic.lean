import Mathlib
import FiniteSimpleGroups.Basic

/-!
# Family 1: Cyclic groups of prime order

The easiest of the five families. `Z/pZ` for `p` prime is simple (its only
subgroups are `{0}` and the whole group, by Lagrange — there's no proper
nontrivial subgroup, let alone normal).

Mathlib has all the pieces:
* `ZMod p` with `[Fact p.Prime]` gives a field, hence a cyclic group of
  order `p` under addition.
* `IsSimpleGroup (ZMod p)` follows from `IsSimpleAddGroup.to_isSimpleGroup`
  applied to the fact that `ZMod p` has no proper nontrivial additive subgroups
  when `p` is prime (Lagrange + prime order).

This is the only family where *every* simple group can be exhibited fully
constructively in Lean today.
-/

namespace FiniteSimpleGroups

variable (p : ℕ) [Fact p.Prime]

/-- `Z/pZ` (as an additive group) is simple for `p` prime. Mathlib has the
ingredients; we cite rather than prove. -/
theorem zmod_prime_isSimpleAddGroup : IsSimpleAddGroup (ZMod p) := by
  sorry -- mathlib: follows from `ZMod p` being a field + `IsSimpleAddGroup` for
        -- additive groups of prime order. Look for `ZMod.isSimpleGroup` or
        -- `IsSimpleAddGroup.of_prime_card`.

/-- The same fact stated multiplicatively. -/
theorem zmod_prime_isSimpleGroup : IsSimpleGroup (Multiplicative (ZMod p)) := by
  sorry

/-- Bundled: `Z/pZ` is a finite simple group. -/
instance zmod_prime_isFSG : IsFSG (Multiplicative (ZMod p)) where
  finite := inferInstance
  nontrivial := by
    haveI : Fact (1 < p) := ⟨Fact.out (p := p.Prime) |>.one_lt⟩
    exact inferInstance
  simple := zmod_prime_isSimpleGroup p

end FiniteSimpleGroups

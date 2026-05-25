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

/-- `Z/pZ` (as an additive group) is simple for `p` prime. Mathlib provides
this directly as `ZMod.instIsSimpleAddGroup` in `Mathlib.GroupTheory.SpecificGroups.Cyclic`. -/
example : IsSimpleAddGroup (ZMod p) := inferInstance

/-- `Z/pZ` viewed multiplicatively is a simple group. Mathlib has
`isSimpleGroup_of_prime_card` for any group of prime cardinality; we apply it
with `Nat.card (Multiplicative (ZMod p)) = Nat.card (ZMod p) = p`
(the equality is definitional since `Multiplicative` is a type alias). -/
theorem zmod_prime_isSimpleGroup : IsSimpleGroup (Multiplicative (ZMod p)) := by
  apply isSimpleGroup_of_prime_card (p := p)
  show Nat.card (ZMod p) = p
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card p

/-- Bundled: `Z/pZ` is a finite simple group. -/
noncomputable instance zmod_prime_isFSG : IsFSG (Multiplicative (ZMod p)) where
  finite := inferInstance
  nontrivial := by
    haveI : Fact (1 < p) := ⟨Fact.out (p := p.Prime) |>.one_lt⟩
    exact inferInstance
  simple := zmod_prime_isSimpleGroup p

end FiniteSimpleGroups

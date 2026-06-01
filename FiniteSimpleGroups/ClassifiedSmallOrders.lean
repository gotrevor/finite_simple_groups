import FiniteSimpleGroups.Classification
import FiniteSimpleGroups.SmallOrders

/-!
# Wiring the `< 60` brick into the CFSG statement

This file connects the bucket-A brick `prime_card_of_simpleGroup_card_lt_sixty`
(SmallOrders) to the classification *conclusion* `IsClassified` (Classification),
via the `isClassified_of_card_prime` bridge.

The result, `isClassified_of_simple_card_lt_sixty`, is the **smallest
fully-discharged window of CFSG**: every finite simple group of order `< 60` is
classified — and this is proved *without* invoking the `CFSG` axiom. The window
is sharp: `A₅` (order 60) is the first simple group requiring a non-cyclic family,
so 60 is exactly where the elementary argument stops.
-/

namespace FiniteSimpleGroups

/-- **Every finite simple group of order `< 60` is classified.**

Such a group has prime order (`prime_card_of_simpleGroup_card_lt_sixty`), so it is
cyclic and lands in the `cyclic` family (`isClassified_of_card_prime`). This is a
sorry-free, `CFSG`-axiom-free discharge of CFSG's conclusion on the order-`< 60`
window — the largest range over which the classification is elementary. -/
theorem isClassified_of_simple_card_lt_sixty {G : Type*} [Group G] [Finite G]
    [Nontrivial G] [IsSimpleGroup G] (h_lt : Nat.card G < 60) : IsClassified G :=
  isClassified_of_card_prime (prime_card_of_simpleGroup_card_lt_sixty h_lt) rfl

end FiniteSimpleGroups

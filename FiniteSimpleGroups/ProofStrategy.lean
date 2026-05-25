import Mathlib
import FiniteSimpleGroups.Basic

/-!
# The CFSG proof strategy

This file states the **architectural milestones** of the CFSG proof. None are
proven (everything is `sorry`); the value is exposing the structure.

The proof of CFSG is not a single argument. It's a *program*, decomposed into
roughly three pillars:

```
                    Feit–Thompson (1962)
                  "every finite simple group
                   has even order, or is Z/pZ"
                            │
                            ▼
                  Aschbacher's dichotomy
                  "groups with involutions are
                  of odd type OR of even type"
                          ╱     ╲
                         ╱       ╲
                        ▼         ▼
                  Odd type      Even type
                  (GLS program)    │
                                   ├── Component type
                                   └── Characteristic 2 type
                                       └── Quasithin
                                           (Aschbacher–Smith 2004)
```

Each milestone is a separate decades-long effort by multiple authors.
-/

namespace FiniteSimpleGroups

/-! ### Milestone 0: Burnside's `p^a q^b` theorem (1904) -/

/-- **Burnside's theorem (1904).** Every finite group whose order has at most
two distinct prime divisors is solvable.

Predates CFSG by half a century but established the technique of using
character theory to constrain group structure. Crucial *psychological* input:
showed that order alone could determine solvability.

Declared as `axiom`. (mathlib may already have a form of this; search
`IsSolvable.of_card_eq_paqb` and similar before relying on this axiom.) -/
axiom Burnside_paqb (G : Type*) [Group G] [Finite G]
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (a b : ℕ)
    (h_card : Nat.card G = p^a * q^b) : IsSolvable G

/-! ### Milestone 1: The Feit-Thompson Odd Order Theorem (1962) -/

/-- **Feit-Thompson Odd Order Theorem.** Every finite group of odd order is
solvable.

* 255-page paper in the *Pacific Journal of Mathematics*, 1963.
* Six-year proof effort by Walter Feit and John Thompson.
* The first major result that made CFSG seem reachable — it lets you focus on
  groups containing involutions (elements of order 2), which is where the
  structure theory bites.
* **Formalized in Coq** by Gonthier et al. in 2013 (six-year effort, ~150,000
  lines). Not yet ported to Lean.

The CFSG-relevant corollary: every nontrivial finite simple group either has
prime order (and is therefore cyclic) or has an involution.

Declared as `axiom` — established in Feit-Thompson 1962 + Gonthier et al.
Coq formalization 2013 (not yet ported to Lean). -/
axiom Feit_Thompson_odd_order (G : Type*) [Group G] [Finite G]
    (h_odd : Odd (Nat.card G)) : IsSolvable G

/-- CFSG-relevant corollary of Feit-Thompson: a nontrivial finite simple group
of odd order is cyclic of prime order.

Declared as `axiom` — derivable from `Feit_Thompson_odd_order` plus the
standard "solvable + simple + nontrivial ⇒ cyclic of prime order" argument. -/
axiom isSimpleGroup_odd_order_iff_prime_cyclic
    (G : Type*) [Group G] [Finite G] [IsSimpleGroup G] [Nontrivial G]
    (h_odd : Odd (Nat.card G)) :
    ∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))

/-! ### Milestone 2: Aschbacher's dichotomy -/

/-- A finite simple group is **of odd type** if its standard component (the
quotient of a centralizer-of-involution by its solvable radical) has odd
characteristic, or if it's one of a small list of sporadics.

Cited in this scaffold as an `opaque` predicate; the full definition is highly
technical (component analysis, B-conjecture, signalizer functor method). -/
opaque IsOddType (G : Type*) [Group G] : Prop

/-- A finite simple group is **of even type** if its standard component has
characteristic 2. The "hard" case for the classification — this is where the
quasithin sub-case lives.

Includes: most Lie-type groups over `F_{2^k}`, the Mathieu groups, a few
other sporadics. -/
opaque IsEvenType (G : Type*) [Group G] : Prop

/-- **Aschbacher's dichotomy (~1980).** Every finite simple group containing
an involution is either of odd type or of even type (the two cases are not
mutually exclusive for small groups, but the cases give complete coverage).

Declared as `axiom` — Aschbacher's program of the 1970s-80s. -/
axiom Aschbacher_dichotomy (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    [Nontrivial G] (h_invol : ∃ x : G, x ≠ 1 ∧ x^2 = 1) :
    IsOddType G ∨ IsEvenType G

/-! ### Milestone 3: The odd-type case (GLS program) -/

/-- **Classification of odd-type simple groups (Gorenstein-Lyons-Solomon program).**
A finite simple group of odd type is isomorphic to a Lie-type group over a
field of odd characteristic, or to one of a small list of sporadics (including
several Janko, Conway, Fischer groups).

The GLS program is the **second-generation** proof — 12 planned volumes
(*The Classification of the Finite Simple Groups*, AMS), of which 10 are
published as of 2023. Rewrites the original proof to fit in a self-contained
sequence. -/
axiom odd_type_classification (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    [Nontrivial G] (h_odd : IsOddType G) :
    True  -- placeholder — would be a structured disjunction over odd-type families

/-! ### Milestone 4: The even-type case -/

/-- A simple group of even type is either of **component type** (its centralizer-
of-involution has a "standard component" generating a Lie-type subgroup over
`F_{2^k}`) or of **characteristic 2 type** (no such component; the whole
analysis happens inside the centralizer's `O_2`). -/
opaque IsComponentType (G : Type*) [Group G] : Prop

/-- The hardest sub-case: **characteristic-2 type without a component** that
fits neatly into one of the standard subcases. -/
opaque IsCharacteristic2Type (G : Type*) [Group G] : Prop

/-- Even-type groups split into component type and characteristic-2 type. -/
axiom even_type_dichotomy (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    [Nontrivial G] (h_even : IsEvenType G) :
    IsComponentType G ∨ IsCharacteristic2Type G

/-! ### Milestone 5: The quasithin case (Aschbacher-Smith, 1990s-2004) -/

/-- A characteristic-2-type simple group is **quasithin** if its "e-value"
(the maximum 2-local 2-rank) is at most 2. This is the case that almost
unraveled CFSG: Mason announced a proof in the early 1980s, but the proof
was found incomplete in the 90s. Aschbacher and Smith re-did it from scratch
in two volumes (~1200 pages, *The Classification of Quasithin Groups* I & II,
AMS 2004) — the last piece of the original CFSG proof to land. -/
opaque IsQuasithin (G : Type*) [Group G] : Prop

/-- **Quasithin classification (Aschbacher-Smith, 2004).** A simple quasithin
group of characteristic-2 type is isomorphic to one of an explicit list of
Lie-type groups over small fields or sporadics.

This theorem's *announcement* is when CFSG was first considered complete
(2004). -/
axiom quasithin_classification (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    [Nontrivial G] (h : IsCharacteristic2Type G) (h_qt : IsQuasithin G) :
    True  -- placeholder for the explicit family enumeration

end FiniteSimpleGroups

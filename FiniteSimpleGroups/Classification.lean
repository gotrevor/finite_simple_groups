import Mathlib
import FiniteSimpleGroups.Basic

/-!
# The Classification of Finite Simple Groups (CFSG)

> **Theorem (CFSG).** Every finite simple group is isomorphic to one of:
> 1. A cyclic group of prime order `Z/pZ`,
> 2. An alternating group `A_n` for some `n ≥ 5`,
> 3. A classical group of Lie type (one of four infinite families: `PSL_n(F_q)`,
>    `PSU_n(F_q)`, `PSp_{2n}(F_q)`, `PΩ^ε_n(F_q)`),
> 4. An exceptional group of Lie type (one of: `G_2(q)`, `F_4(q)`, `E_6(q)`,
>    `E_7(q)`, `E_8(q)`, or one of the twisted forms `²B_2`, `²G_2`, `²F_4`,
>    `³D_4`, `²E_6`),
> 5. One of the **26 sporadic groups** (Mathieu × 5, Janko × 4, Conway × 3,
>    Fischer × 3, Monster + Baby Monster + 11 others — see `Sporadics`).

This was completed between roughly 1955 and 2004, with the **second-generation
proof** (Gorenstein-Lyons-Solomon program) still being written down — 10 of
12 planned volumes published as of 2023.

This file states the theorem as a single disjunction. The disjuncts are
proven (or sorry'd) in the per-family modules.
-/

namespace FiniteSimpleGroups

/-- One of the four classical Lie-type families (placeholder; see `LieType`). -/
opaque ClassicalLieType (G : Type*) [Group G] : Prop

/-- One of the exceptional Lie-type groups (placeholder; see `Exceptional`). -/
opaque ExceptionalLieType (G : Type*) [Group G] : Prop

/-- One of the 26 sporadic simple groups (placeholder; see `Sporadics`). -/
opaque Sporadic (G : Type*) [Group G] : Prop

/-- The CFSG predicate: `G` is isomorphic to one of the canonical families. -/
inductive IsClassified (G : Type*) [Group G] : Prop where
  | cyclic : (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) → IsClassified G
  | alternating : (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) → IsClassified G
  | classicalLieType : ClassicalLieType G → IsClassified G
  | exceptionalLieType : ExceptionalLieType G → IsClassified G
  | sporadic : Sporadic G → IsClassified G

/-- **The Classification Theorem.** Every finite simple group is classified.

This statement is the entire point of CFSG. Its proof spans tens of thousands
of pages across hundreds of papers (1955-2004), with the second-generation
self-contained proof still being written (10 of 12 volumes by 2023).

Declared as an `axiom` — established in the math literature; not realistically
formalizable in any proof assistant for years to come. -/
axiom CFSG (G : Type*) [Group G] [IsFSG G] : IsClassified G

end FiniteSimpleGroups

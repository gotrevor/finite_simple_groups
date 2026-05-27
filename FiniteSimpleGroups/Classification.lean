import Mathlib
import FiniteSimpleGroups.Basic
import FiniteSimpleGroups.LieType
import FiniteSimpleGroups.Exceptional
import FiniteSimpleGroups.Sporadics

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

## What this file states

`IsClassified G` is a five-way disjunction matching the families above. Each
disjunct quantifies over the family parameters and asserts an isomorphism
from `G` to a specific group in that family.

**Inc 28 (2026-05-26):** Tightened the Lie-type and sporadic disjuncts. They
used to route through `opaque ... : Prop` placeholders (effectively content-
free). They now quantify over the parameterized carriers introduced in Inc 28:
`classicalLieTypeCarrier fam n q`, `exceptionalLieTypeCarrier fam k`, and
`Sporadics.Name.carrier name`. The carriers themselves remain opaque (no
construction yet), but the *statement* of CFSG is now meaningful — it asserts
existence of specific (family, parameter) data and a group isomorphism.
-/

namespace FiniteSimpleGroups

/-- The CFSG predicate: `G` is isomorphic to one of the canonical families.

Each disjunct except `cyclic` requires the target carrier to carry a `Group`
instance (the carriers are opaque pending construction; the instance is
existentially asserted alongside the isomorphism). -/
inductive IsClassified (G : Type*) [Group G] : Prop where
  | cyclic :
      (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) →
      IsClassified G
  | alternating :
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) →
      IsClassified G
  | classicalLieType :
      (∃ (fam : ClassicalFamily) (n q : ℕ)
         (_ : Group (classicalLieTypeCarrier fam n q)),
        Nonempty (G ≃* classicalLieTypeCarrier fam n q)) →
      IsClassified G
  | exceptionalLieType :
      (∃ (fam : ExceptionalFamily) (k : ℕ)
         (_ : Group (exceptionalLieTypeCarrier fam k)),
        Nonempty (G ≃* exceptionalLieTypeCarrier fam k)) →
      IsClassified G
  | sporadic :
      (∃ (name : Sporadics.Name)
         (_ : Group name.carrier),
        Nonempty (G ≃* name.carrier)) →
      IsClassified G

/-- **The Classification Theorem.** Every finite simple group is classified.

This statement is the entire point of CFSG. Its proof spans tens of thousands
of pages across hundreds of papers (1955-2004), with the second-generation
self-contained proof still being written (10 of 12 volumes by 2023).

Declared as an `axiom` — established in the math literature; not realistically
formalizable in any proof assistant for years to come. -/
axiom CFSG (G : Type*) [Group G] [IsFSG G] : IsClassified G

end FiniteSimpleGroups

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

**Order-pin (2026-06-02):** the `sporadic` disjunct additionally asserts
`Nat.card name.carrier = name.order` (the ATLAS order). This is the cheapest
*faithfulness anchor* on the opaque carriers: any eventual construction whose
cardinality disagrees with the ATLAS value trips a contradiction, so a wrong
carrier can't silently satisfy CFSG. It does not de-opaque the carrier (that is
*definitional* debt), but it constrains it. The same pin is the natural next
step for the Lie-type disjuncts (carrier order as a function of `(fam, n, q)`).
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
        Nat.card name.carrier = name.order ∧
        Nonempty (G ≃* name.carrier)) →
      IsClassified G

/-!
## The Classification Theorem itself

Every finite simple group is classified — `IsClassified G` for `[IsFSG G]`. This
is the entire point of CFSG; its mathematical proof spans tens of thousands of
pages (1955–2004, second-generation proof still being written down).

Rather than assert it as a bare `axiom` here (which would hide the proof's whole
structure behind one opaque word), it is **proven as the theorem `CFSG`** in
`ProofStrategy.lean`, by assembling the named program milestones (Feit–Thompson,
Aschbacher's dichotomy, and the odd/even/component/char-2/quasithin
classifications) via `classification_via_program`. Those milestones stay honest
`axiom`s — they are the genuinely-deep inputs — but the *deductive skeleton*
connecting them to the conclusion is machine-checked.

The payoff: `#print axioms CFSG` itemizes the real mathematical debt (the 7
milestone axioms + the standard trio), instead of a single monolithic assertion.
-/

/-- **Bridge: prime order ⟹ classified.** A finite group of prime order `p` is
cyclic (`isCyclic_of_prime_card`), hence isomorphic to `Multiplicative (ZMod p)`,
so it lands in the `cyclic` family of `IsClassified`. No simplicity hypothesis is
needed — prime order alone forces cyclicity.

This is a genuine (sorry-free, `CFSG`-axiom-free) discharge of the classification
*conclusion* for the cyclic family, reusing the same `mulEquivOfPrimeCardEq` route
as `ProofStrategy.feitThompson_dichotomy`. -/
theorem isClassified_of_card_prime {G : Type*} [Group G] {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card G = p) : IsClassified G := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine IsClassified.cyclic ⟨p, hp, ⟨?_⟩⟩
  have hH : Nat.card (Multiplicative (ZMod p)) = p := by simp
  exact mulEquivOfPrimeCardEq hcard hH

end FiniteSimpleGroups

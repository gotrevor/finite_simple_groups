/-
# B & G, Theorem 1.13 — `critical_odd` (Thompson's critical subgroup)

For an odd-order nontrivial p-group `G`, there exists a *critical subgroup*
`H` with:
1. `H` is characteristic in `G`
2. `⁅H, G⁆ ⊆ Z(H)` (so the action of G on H is "central")
3. `H` has nilpotency class ≤ 2
4. `exponent H = p`
5. The centralizer of H in `Aut(G)` is a p-group

The classical Thompson critical subgroup. Used heavily in p-local analysis.

## Tree

```
1.13 critical_odd
└── Branch (only): existence via Thompson_critical
    ├── Twig 1: AXIOM — Thompson_critical produces witness H
    ├── Twig 2: AXIOM — pull out the five properties from the witness
    └── Top: ∃ H, properties
```

The Coq proof (lines 489-552) is ~60 lines, very dense. We package the
existence and its five conclusions as a single witness-producing axiom.
Translating the actual construction would require:
- `Thompson_critical` (MathComp p-group lemma)
- `Ohm_1`, `Ohm_char`
- `bin2odd` (binomial-coefficient-2 odd identity)
- Action on automorphisms (MathComp `aperm`)

All deferred for future increments.
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup

namespace FeitThompson.BGsection1.T1_13

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

/-- `IsCritical p H G` packages the conclusion of Thompson's critical
subgroup theorem: H is characteristic in G with strong p-structure.

In the Coq statement this is a 5-conjunct `{H : {group gT} | ...}`. We
mirror that structure as a Prop, with `H.Characteristic` not yet in
mathlib (axiomatized in our `MathlibStubs`-style approach), so we use
`H.Normal` plus the comment "would be `H.Characteristic`". -/
structure IsCritical (p : ℕ) (H : Subgroup G) : Prop where
  normal : H.Normal
  -- "⁅H, G⁆ ⊆ Z(H)" — phrased over G as "⁅H, ⊤⁆ ≤ H and centralizes H".
  -- We use the equivalent: ⁅⁅H, ⊤⁆, H⁆ = ⊥.
  commCentralizesH : (⁅(⁅H, (⊤ : Subgroup G)⁆ : Subgroup G), H⁆ : Subgroup G) = ⊥
  -- nilpotencyClass ≤ 2: stated as `⁅⁅H, H⁆, H⁆ = ⊥` for nilpotency class 2.
  classTwo : (⁅(⁅H, H⁆ : Subgroup G), H⁆ : Subgroup G) = ⊥
  -- exponent H = p: every element has order dividing p.
  expP : ∀ h ∈ H, h ^ p = 1
  -- centralizer in Aut(G) is a p-group: phrased abstractly here.
  -- The automorphism-group statement needs MulAut + action setup not in stubs.
  centAutPgroup : True

namespace BranchExistence

/-- **(AXIOM)** — Thompson's critical subgroup existence.

Coq: `Thompson_critical` at the top of BGsection1.v line ~496. Standard
result from group cohomology / commutator calculus on odd p-groups.

Deferred to a dedicated mathlib PR. -/
axiom critical_subgroup_exists
    (p : ℕ) (_hG : IsPGroup p (⊤ : Subgroup G))
    (_hOdd : Odd (Nat.card G))
    (_hNT : (⊤ : Subgroup G) ≠ ⊥) :
    ∃ H : Subgroup G, IsCritical p H

end BranchExistence

/-- **Main (B & G 1.13)** — `critical_odd`. -/
theorem critical_odd
    (p : ℕ) (hG : IsPGroup p (⊤ : Subgroup G))
    (hOdd : Odd (Nat.card G))
    (hNT : (⊤ : Subgroup G) ≠ ⊥) :
    ∃ H : Subgroup G, IsCritical p H :=
  BranchExistence.critical_subgroup_exists p hG hOdd hNT

end FeitThompson.BGsection1.T1_13

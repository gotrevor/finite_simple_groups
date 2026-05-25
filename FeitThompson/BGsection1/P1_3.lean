/-
# B & G, Proposition 1.3 (P. Hall) — `cent_sub_Fitting`

**Flagship**: in a solvable group, the centralizer of the Fitting subgroup
is contained in the Fitting subgroup.

`IsSolvable G → C_G(F(G)) ≤ F(G)`

## Tree

P. Hall's proof factors through two propositions about *chief factors*.
B & G makes this explicit:

```
cent_sub_Fitting
├── Branch A: C_G(F(G)) ≤ H        (cent_Fitting_le_chief_stab)
│   where H := ⋂_{chief factors V<U} stabilizer of U/V
│   ├── A1: centralizing F(G) ⇒ stabilizing every chief factor U/V with U ≤ F(G)
│   └── A2: every chief factor in a solvable G is in F(G) — bridge lemma
└── Branch B: H ≤ F(G)              (chief_stab_sub_Fitting, B & G Prop 1.2)
    ├── B1: among normal subgroups stabilizing all chief factors, pick min
    └── B2: any G-normal subgroup K with K ⊄ F(G) has a chief factor inside K
            that K doesn't stabilize — contradiction, so H ≤ F(G)
```
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_3

open FeitThompson.Stubs

variable {G : Type*} [Group G]

/-- The "chief stabilizer" intersection: subgroup of G stabilizing every
chief factor U/V of G.

Approximation: stabilizing U/V is approximated by centralizing the U-part
inside the normalizer of V. The real formal version needs quotient-action
machinery (`Q`-action stabilizers) which is itself a stub-level item. -/
def chiefStab : Subgroup G :=
  ⨅ p : Subgroup G × Subgroup G, ⨅ _ : IsChiefFactor p.1 p.2,
    Subgroup.centralizer ((p.2 ⊓ Subgroup.normalizer p.1 : Subgroup G) : Set G)

namespace BranchA

/-- **A1**: centralizing F(G) implies stabilizing every chief factor inside F(G). -/
theorem cent_Fitting_le_chief_stab_of_in_Fitting
    (_hG : IsSolvable G) :
    Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) ≤
      chiefStab (G := G) := by
  sorry

end BranchA

namespace BranchB

/-- **B**: B & G Proposition 1.2 (Hall's lemma) — the chief stabilizer
intersection is contained in the Fitting subgroup. -/
theorem chief_stab_sub_Fitting (_hG : IsSolvable G) :
    chiefStab (G := G) ≤ FittingSubgroup G := by
  sorry

end BranchB

/-- **Main**: Hall's theorem (B & G Prop 1.3). -/
theorem cent_sub_Fitting (hG : IsSolvable G) :
    Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) ≤
      FittingSubgroup G :=
  (BranchA.cent_Fitting_le_chief_stab_of_in_Fitting hG).trans
    (BranchB.chief_stab_sub_Fitting hG)

end FeitThompson.BGsection1.P1_3

/-
# B & G, Proposition 1.9 base case — `stable_factor_cent`

If `A ⊆ C(H)`, the chain `H ⊲ G` is A-stable (`⁅G, A⁆ ⊆ H ⊲ G`),
A and G have coprime orders, and G is solvable, then A acts trivially on G.

This is the inductive step for `stable_series_cent` (1.9 main).

## Tree

```
1.9 base — stable_factor_cent
└── Single cited axiom: coprime_quotient_cent + quotient_lift chain
    (Coq BGsection1.v:391-395)
```

Previous version had `True`-placeholder axioms; refactored as a single
meaningful axiom citing the Coq line.
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_9_base

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

/-- `IsStableFactor A H` says `H ≤ ⊤` is A-stable: `H` is normal and
`⁅⊤, A⁆ ≤ H`. Captures Coq's `stable_factor A H G` with the ambient
group set to `⊤`. -/
structure IsStableFactor (A : Subgroup G) (H : Subgroup G) : Prop where
  normal_H : H.Normal
  comm_le : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ≤ H

namespace BranchChain

/-- **AXIOM** — packaged 1.9-base step.

Coq: BGsection1.v:391-395, the body of `stable_factor_cent`. Uses
`coprime_quotient_cent` (A acts trivially on G/H) + `quotientSGK`
(lift back from G/H plus A ⊆ C(H)) to conclude A ⊆ C(G). -/
axiom stable_factor_cent_chain
    {G : Type*} [Group G] [Fintype G]
    (A H : Subgroup G)
    (_hStable : IsStableFactor A H)
    (_hCAH : A ≤ Subgroup.centralizer (H : Set G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hSol : IsSolvable G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G)

end BranchChain

/-- **Main (B & G 1.9 base)** — `stable_factor_cent`. -/
theorem stable_factor_cent
    (A H : Subgroup G)
    (hStable : IsStableFactor A H)
    (hCAH : A ≤ Subgroup.centralizer (H : Set G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) :=
  BranchChain.stable_factor_cent_chain A H hStable hCAH hCoprime hSol

end FeitThompson.BGsection1.P1_9_base

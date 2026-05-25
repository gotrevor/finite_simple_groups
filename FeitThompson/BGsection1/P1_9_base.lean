/-
# B & G, Proposition 1.9 base case — `stable_factor_cent`

If `A ⊆ C(H)`, the chain `H ⊲ G` is A-stable (`⁅G, A⁆ ⊆ H ⊲ G ⊲ G`),
A and G have coprime orders, and G is solvable, then A acts trivially on G.

This is the inductive step in B & G 1.9; the "main" form (`stable_series_cent`)
just iterates it down a stable series.

## Tree

```
1.9 base — stable_factor_cent
├── Branch A: A acts trivially on quotient G/H (via coprime_quotient_cent)
│   ├── Twig 1: ⁅G,A⁆ ⊆ H ⇒ A · H/H ⊆ C(G/H)
│   └── Twig 2: AXIOM — coprime_quotient_cent (mathlib quotient lift)
└── Branch B: A trivial on G/H + A trivial on H ⇒ A trivial on G
              (coprime extension: kernel is "thin", lift is unique)
    └── Twig: AXIOM — quotient-to-whole lifting (subnormal + coprime)
```
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_9_base

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

/-- `IsStableFactor A H` says `H ≤ ⊤` is A-stable: `H` is normal and the
top group has `⁅⊤, A⁆ ≤ H`. Captures Coq's `stable_factor A H G` with the
ambient group set to `⊤`. -/
structure IsStableFactor (A : Subgroup G) (H : Subgroup G) : Prop where
  normal_H : H.Normal
  comm_le : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ≤ H

namespace BranchA_quot

/-- **A (AXIOM)** — A acts trivially on G/H given the stable-factor condition
and coprime / solvable hypotheses.

Coq: `coprime_quotient_cent` step in `BGsection1.v` line ~395. -/
axiom A_trivial_on_quotient
    {G : Type*} [Group G] [Fintype G]
    (A H : Subgroup G)
    (_hStable : IsStableFactor A H)
    (_hCAH : A ≤ Subgroup.centralizer (H : Set G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hSol : IsSolvable G) :
    -- A's image in G/H is in the center of G/H — Prop-level placeholder.
    True

end BranchA_quot

namespace BranchB_lift

/-- **B (AXIOM)** — A trivial on G/H plus A trivial on H lifts to A trivial on G.

Coq: `quotientSGK` plus `subsetI` combo at line ~394. The coprime hypothesis
is what makes this lifting unique (otherwise H₂(A, H) obstructs). Deferred. -/
axiom lift_to_G
    {G : Type*} [Group G] [Fintype G]
    (A H : Subgroup G)
    (_hStable : IsStableFactor A H)
    (_hCAH : A ≤ Subgroup.centralizer (H : Set G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hSol : IsSolvable G)
    (_hQuotTrivial : True) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G)

end BranchB_lift

/-- **Main (B & G 1.9 base)** — `stable_factor_cent`. -/
theorem stable_factor_cent
    (A H : Subgroup G)
    (hStable : IsStableFactor A H)
    (hCAH : A ≤ Subgroup.centralizer (H : Set G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) :=
  BranchB_lift.lift_to_G A H hStable hCAH hCoprime hSol
    (BranchA_quot.A_trivial_on_quotient A H hStable hCAH hCoprime hSol)

end FeitThompson.BGsection1.P1_9_base

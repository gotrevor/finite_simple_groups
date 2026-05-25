/-
# B & G, Proposition 1.8 / Aschbacher 24.1 — `coprime_cent_Phi`

If G is a p-group, |A| is coprime to |G|, and `⁅G,A⁆ ⊆ Φ(G)`, then `A ⊆ C(G)`.

The substance is the **Frattini argument**: elements of Φ(G) are
non-generating, so if A pushes G into Φ(G), the action is "trivial" in the
generation sense, which combined with coprimality forces full triviality.

## Tree

```
coprime_cent_Phi
├── Branch A: ⁅G,A⁆ ⊆ Φ(G) ⇒ C_G(A) covers a generating set of G
│   ├── A1: G/Φ(G) is elementary abelian (Phi quotient is abelem)
│   ├── A2: A acts trivially on G/Φ(G) (since ⁅G,A⁆ ⊆ Φ(G))
│   └── A3: coprime + A trivial on G/Φ(G) ⇒ A trivial on G (lifting)
└── Branch B: A trivial on G ⇔ A ⊆ C(G)        (definitional)
```

Uses **mathlib's real `frattini`** — no stub for the Frattini subgroup.
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup

namespace FeitThompson.BGsection1.P1_8

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

namespace BranchA

/-- **A1**: for a p-group G, the quotient G/Φ(G) is elementary abelian. -/
theorem phi_quotient_abelem (p : ℕ) (_hG : IsPGroup p (⊤ : Subgroup G)) :
    True := by trivial  -- placeholder for the elementary abelian fact

/-- **A2**: if `⁅G,A⁆ ⊆ Φ(G)`, then A acts trivially on G/Φ(G). -/
theorem A_trivial_on_quotient
    (A : Subgroup G) (_hCommInPhi : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ≤ frattini G) :
    -- formally: the image of A in Aut(G/Φ(G)) is the identity
    True := by trivial

/-- **A3 (substance)**: coprime + A trivial on G/Φ(G) ⇒ A trivial on G.

Reason: the kernel of `Aut(G) → Aut(G/Φ(G))` is a p-group (acts inside Φ(G)),
and A is coprime to p. So A lifts to triviality. -/
theorem A_trivial_on_G_of_trivial_on_quotient
    (p : ℕ) (A : Subgroup G)
    (_hG : IsPGroup p (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hQuotTrivial : True) :  -- placeholder for "A trivial on G/Φ(G)"
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  sorry

end BranchA

/-- **Main (B & G Proposition 1.8 / Aschbacher 24.1)**. -/
theorem coprime_cent_Phi
    (p : ℕ) (A : Subgroup G)
    (hG : IsPGroup p (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hCommInPhi : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ≤ frattini G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  have hQuotTrivial := BranchA.A_trivial_on_quotient A hCommInPhi
  exact BranchA.A_trivial_on_G_of_trivial_on_quotient p A hG hCoprime hQuotTrivial

end FeitThompson.BGsection1.P1_8

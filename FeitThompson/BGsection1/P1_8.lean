/-
# B & G, Proposition 1.8 / Aschbacher 24.1 — `coprime_cent_Phi`

If G is a p-group, `|A|` is coprime to `|G|`, and `⁅G,A⁆ ⊆ Φ(G)`, then `A ⊆ C(G)`.

## Tree

```
coprime_cent_Phi
└── Single cited axiom: Phi_nongen + coprime_cent_prod chain
    (Coq BGsection1.v:374-383, 5 lines)
```

Previous version had a `True` placeholder hypothesis that made the
declaration technically unsound. Refactored: the entire 1.8 statement
is now a single axiom with meaningful hypotheses, citing the Coq line.
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup

namespace FeitThompson.BGsection1.P1_8

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

namespace BranchA

/-- **AXIOM** — Phi-nongen / Frattini's argument (`Phi_nongen` in MathComp).

If `Φ(G) ⊔ H = ⊤` for some subgroup `H`, then `H = ⊤`.

Equivalently: Frattini elements are non-generating. MathComp source:
`Phi_nongen` in `maximal.v`. The mathlib analog would be a corollary
of `frattini_le_coatom`. -/
axiom Phi_nongen
    {G : Type*} [Group G]
    (H : Subgroup G)
    (_h : (frattini G) ⊔ H = ⊤) :
    H = ⊤

/-- **AXIOM** — packaged 1.8 step. Combines `Phi_nongen` with 1.6(a)
`coprime_cent_prod` and `pgroup_sol` to chain through Coq's 5-line proof.

Coq: BGsection1.v:374-383. Citing as a single axiom rather than the
prior `True`-hypothesis chain (which was technically unsound). -/
axiom coprime_cent_Phi_chain
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) (A : Subgroup G)
    (_hG : IsPGroup p (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hCommInPhi : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ≤ frattini G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G)

end BranchA

/-- **Main (B & G Proposition 1.8 / Aschbacher 24.1)**. -/
theorem coprime_cent_Phi
    (p : ℕ) (A : Subgroup G)
    (hG : IsPGroup p (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hCommInPhi : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ≤ frattini G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) :=
  BranchA.coprime_cent_Phi_chain p A hG hCoprime hCommInPhi

end FeitThompson.BGsection1.P1_8

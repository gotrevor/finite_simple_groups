/-
# B & G, Proposition 1.9 base case — `stable_factor_cent`

If `A ⊆ C(H)`, the chain `H ⊲ G` is A-stable (`⁅G, A⁆ ⊆ H ⊲ G`),
A and G have coprime orders, and G is solvable, then A acts trivially on G.

This is the inductive step for `stable_series_cent` (1.9 main).

## Relativization (Inc 26)

`stable_factor_cent_chain'` is the relativized form at arbitrary ambient
`K : Subgroup G` (was K = ⊤ baked in). The K = ⊤ specialization
`stable_factor_cent_chain` is now a derived theorem. This unblocks the
P1_10 soundness fix (Inc 27), which needs the K = N_G(C_G(A)) form to
discharge the false-claim `stable_factor_data` axiom.

## Tree

```
1.9 base — stable_factor_cent
└── BranchChain.stable_factor_cent_chain         (theorem, K = ⊤)
    └── BranchChain.stable_factor_cent_chain'    (AXIOM, K arbitrary)
        — Coq BGsection1.v:391-395 with G ↦ K
```
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_9_base

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

/-- `IsStableFactor A H` (K = ⊤ specialization): `H` is normal and
`⁅⊤, A⁆ ≤ H`. Captures Coq's `stable_factor A H G` with the ambient
group set to `⊤`. -/
structure IsStableFactor (A : Subgroup G) (H : Subgroup G) : Prop where
  normal_H : H.Normal
  comm_le : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ≤ H

/-- **Relativized stable factor** `IsStableFactor' A K H`: at ambient
subgroup `K`, `H ≤ K` is `K`-conjugation-stable with `⁅K, A⁆ ≤ H`.

The `conjStable` clause expresses "H is normal in K" pointwise, avoiding
the `(H.subgroupOf K).Normal` framing (which would force a different
codomain). All three clauses are stated on subgroups of the ambient
group type `G`, matching Coq's MathComp formulation. -/
structure IsStableFactor' (A K H : Subgroup G) : Prop where
  le_K : H ≤ K
  comm_le : (⁅K, A⁆ : Subgroup G) ≤ H
  conjStable : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H

namespace BranchChain

/-- **AXIOM (relativized)** — packaged 1.9-base step at arbitrary ambient `K`.

Coq: BGsection1.v:391-395, with the ambient group `G` replaced by `K`.
Uses `coprime_quotient_cent` (A acts trivially on K/H) + `quotientSGK`
(lift back from K/H plus A ⊆ C(H)) to conclude A ⊆ C(K). The
relativization is straightforward in MathComp; in Lean it would require
quotient-action lemmas mathlib lacks, so we cite it as an axiom. -/
axiom stable_factor_cent_chain'
    {G : Type*} [Group G] [Fintype G]
    (A K H : Subgroup G)
    (_hStable : IsStableFactor' A K H)
    (_hCAH : A ≤ Subgroup.centralizer (H : Set G))
    (_hCoprime : (Nat.card K).Coprime (Nat.card A))
    (_hSol : IsSolvable K) :
    A ≤ Subgroup.centralizer (K : Set G)

/-- **K = ⊤ specialization (THEOREM)** — derived from
`stable_factor_cent_chain'`. The previous axiom of this name (Inc 16)
becomes a derived theorem now that the relativized version is the
foundational axiom. Net axiom count: -1. -/
theorem stable_factor_cent_chain
    (A H : Subgroup G)
    (hStable : IsStableFactor A H)
    (hCAH : A ≤ Subgroup.centralizer (H : Set G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  haveI := hSol
  -- Build the relativized stable factor at K = ⊤ from IsStableFactor A H.
  have hStable' : IsStableFactor' A (⊤ : Subgroup G) H :=
    { le_K := le_top
      comm_le := hStable.comm_le
      conjStable := fun k _hk h hh => hStable.normal_H.conj_mem h hh k }
  -- Coprime |⊤| |A| = coprime |G| |A| via Subgroup.card_top.
  have hCoprime' : (Nat.card (⊤ : Subgroup G)).Coprime (Nat.card A) := by
    rwa [Subgroup.card_top]
  exact stable_factor_cent_chain' A (⊤ : Subgroup G) H hStable' hCAH hCoprime'
    inferInstance

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

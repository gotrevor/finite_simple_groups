/-
# B & G, Proposition 1.6 (a), (b), (c) — coprime commutator chain

Three related lemmas that chain:

- `coprime_cent_prod`        (1.6a):  `⁅G,A⁆ · C_G(A) = G`
- `coprime_commGid`          (1.6b):  `⁅⁅G,A⁆, A⁆ = ⁅G,A⁆`
- `coprime_commGG1P`         (1.6c):  `⁅⁅G,A⁆, A⁆ = ⊥ → A ≤ C(G)`

All under the hypotheses: `A ⊆ N(G)`, `coprime |G| |A|`, `solvable G`.

## Tree (chained)

```
1.6(a) coprime_cent_prod
├── Branch A: stronger variant 1.6(a') coprimeR_cent_prod
│             (replaces |G| with |⁅G,A⁆| in coprime hypothesis)
└── Branch B: descend via Lagrange (|G| = |⁅G,A⁆| × [G : ⁅G,A⁆])

1.6(b) coprime_commGid — uses 1.6(a) on ⁅G,A⁆ instead of G
├── Twig 1: ⁅G,A⁆ is itself A-normalized (commutator is normal-stable)
├── Twig 2: Apply 1.6(a) to ⁅G,A⁆: ⁅⁅G,A⁆,A⁆ · C_{⁅G,A⁆}(A) = ⁅G,A⁆
└── Twig 3: C_{⁅G,A⁆}(A) ≤ C(A) acts trivially on ⁅G,A⁆ ⇒ projects out
            (Lagrange-style reasoning collapses centralizer term to ⊥)

1.6(c) coprime_commGG1P — direct from 1.6(b)
└── Twig: ⁅⁅G,A⁆,A⁆ = ⊥ + 1.6(b) ⇒ ⁅G,A⁆ = ⊥ ⇒ A ≤ C(G)
```
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_6

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

namespace BranchA_coprimeR

/-- **1.6(a'), `coprimeR_cent_prod`** — stronger variant with |⁅G,A⁆| in
the coprime hypothesis. -/
theorem coprimeR_cent_prod
    (A : Subgroup G)
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card (⁅(⊤ : Subgroup G), A⁆ : Subgroup G)).Coprime (Nat.card A))
    (_hSol : IsSolvable (⁅(⊤ : Subgroup G), A⁆ : Subgroup G)) :
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
      Subgroup.centralizer (A : Set G) = ⊤ := by
  sorry

end BranchA_coprimeR

/-- **1.6(a) `coprime_cent_prod`**: from coprimeR via Lagrange. -/
theorem coprime_cent_prod
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hSol : IsSolvable G) :
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
      Subgroup.centralizer (A : Set G) = ⊤ := by
  apply BranchA_coprimeR.coprimeR_cent_prod A hNorm
  · -- coprime |⁅G,A⁆| |A| follows from coprime |G| |A| since ⁅G,A⁆ ≤ G
    sorry
  · -- solvable ⁅G,A⁆ follows from solvable G since ⁅G,A⁆ ≤ G
    sorry

/-- **1.6(b) `coprime_commGid`**: `⁅⁅G,A⁆, A⁆ = ⁅G,A⁆`.

Applies 1.6(a) to the subgroup `⁅G,A⁆` viewed as a normal-by-A subgroup. -/
theorem coprime_commGid
    (A : Subgroup G)
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hSol : IsSolvable G) :
    ⁅(⁅(⊤ : Subgroup G), A⁆ : Subgroup G), A⁆ = ⁅(⊤ : Subgroup G), A⁆ := by
  -- The full proof applies 1.6(a) to ⁅G,A⁆ instead of G and uses the
  -- normality of ⁅G,A⁆ under A. The collapse of the centralizer-of-A term
  -- inside ⁅G,A⁆ to ⊥ is the substantive step.
  sorry

/-- **1.6(c) `coprime_commGG1P`**: vanishing of ⁅⁅G,A⁆, A⁆ forces A ≤ C(G). -/
theorem coprime_commGG1P
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G)
    (hVanish : ⁅(⁅(⊤ : Subgroup G), A⁆ : Subgroup G), A⁆ = ⊥) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  -- 1.6(b) plus hVanish ⇒ ⁅G,A⁆ = ⊥, which equivalently says A ≤ C(G).
  have hId : ⁅(⁅(⊤ : Subgroup G), A⁆ : Subgroup G), A⁆ = ⁅(⊤ : Subgroup G), A⁆ :=
    coprime_commGid A hNorm hCoprime hSol
  have hCommBot : ⁅(⊤ : Subgroup G), A⁆ = ⊥ := by
    rw [← hId]; exact hVanish
  -- ⁅G, A⁆ = ⊥ ↔ A centralizes G (the iff is in mathlib as a commutator-eq-bot lemma)
  sorry

end FeitThompson.BGsection1.P1_6

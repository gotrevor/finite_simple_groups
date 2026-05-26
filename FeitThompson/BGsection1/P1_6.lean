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
import FeitThompson.CommutatorExtras
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_6

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

namespace BranchA_coprimeR

/-- **1.6(a'), `coprimeR_cent_prod` (AXIOM)** — stronger variant with |⁅G,A⁆|
in the coprime hypothesis.

Coq: BGsection1.v line ~301. The Coq proof uses `coprime_norm_quotient_cent`
and `quotient_cents2r` — quotient-action lemmas we don't have in Lean. -/
axiom coprimeR_cent_prod
    {G : Type*} [Group G] [Fintype G]
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card (⁅(⊤ : Subgroup G), A⁆ : Subgroup G)).Coprime (Nat.card A))
    (hSol : IsSolvable (⁅(⊤ : Subgroup G), A⁆ : Subgroup G)) :
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
      Subgroup.centralizer (A : Set G) = ⊤

end BranchA_coprimeR

/-- **1.6(a) `coprime_cent_prod`**: from coprimeR via Lagrange. -/
theorem coprime_cent_prod
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
      Subgroup.centralizer (A : Set G) = ⊤ := by
  haveI := hSol
  apply BranchA_coprimeR.coprimeR_cent_prod A hNorm
  · -- coprime |⁅⊤,A⁆| |A| from coprime |G| |A|: |⁅⊤,A⁆| ∣ |⊤| = |G|
    have hCard : Nat.card (↥(⁅(⊤ : Subgroup G), A⁆)) ∣ Nat.card G := by
      have h1 : Nat.card (↥(⁅(⊤ : Subgroup G), A⁆)) ∣ Nat.card (↥(⊤ : Subgroup G)) :=
        Subgroup.card_dvd_of_le le_top
      have h2 : Nat.card (↥(⊤ : Subgroup G)) = Nat.card G :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      exact h2 ▸ h1
    exact hCoprime.of_dvd_left hCard
  · -- IsSolvable ⁅⊤,A⁆ from IsSolvable G (subgroups inherit solvability)
    infer_instance

/-- **1.6(b) `coprime_commGid`**: `⁅⁅G,A⁆, A⁆ = ⁅G,A⁆`.

Coq: BGsection1.v line ~322. Translation strategy (faithful to upstream):

1. (⊆) `Subgroup.commutator_mono` since `⁅⊤,A⁆ ≤ ⊤`.
2. (⊇) Rewrite `⊤ = ⁅⊤,A⁆ ⊔ C_G(A)` via `coprime_cent_prod`, then apply
   `commutator_sup_le` (= MathComp `commMG`, axiomatized in
   `CommutatorExtras`). The `⁅C_G(A), A⁆` term collapses to `⊥` by
   `commutator_eq_bot_iff_le_centralizer` since `C_G(A) ≤ C_G(A)`. -/
theorem coprime_commGid
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    ⁅(⁅(⊤ : Subgroup G), A⁆ : Subgroup G), A⁆ = ⁅(⊤ : Subgroup G), A⁆ := by
  refine le_antisymm ?_ ?_
  · -- (⊆) ⁅⁅⊤,A⁆, A⁆ ≤ ⁅⊤,A⁆ by monotonicity (⁅⊤,A⁆ ≤ ⊤).
    exact Subgroup.commutator_mono le_top le_rfl
  · -- (⊇) ⁅⊤,A⁆ ≤ ⁅⁅⊤,A⁆, A⁆.
    -- Step 1: ⊤ = ⁅⊤,A⁆ ⊔ C_G(A) from coprime_cent_prod.
    have hSup : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
        Subgroup.centralizer (A : Set G) = ⊤ :=
      coprime_cent_prod A hNorm hCoprime hSol
    -- Step 2: rewrite ⁅⊤, A⁆ as ⁅⁅⊤,A⁆ ⊔ C_G(A), A⁆.
    calc (⁅(⊤ : Subgroup G), A⁆ : Subgroup G)
        = ⁅((⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
              Subgroup.centralizer (A : Set G)), A⁆ := by rw [hSup]
      _ ≤ ⁅(⁅(⊤ : Subgroup G), A⁆ : Subgroup G), A⁆ ⊔
            ⁅Subgroup.centralizer (A : Set G), A⁆ := by
          -- Step 3: apply commutator_sup_le with the two normalization side conditions.
          exact FeitThompson.CommutatorExtras.commutator_sup_le _ _ _
            (FeitThompson.CommutatorExtras.commg_normr A)
            (FeitThompson.CommutatorExtras.le_normalizer_centralizer A)
      _ = ⁅(⁅(⊤ : Subgroup G), A⁆ : Subgroup G), A⁆ ⊔ ⊥ := by
          -- Step 4: ⁅C_G(A), A⁆ = ⊥ since C_G(A) ≤ C_G(A).
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl]
      _ = ⁅(⁅(⊤ : Subgroup G), A⁆ : Subgroup G), A⁆ := sup_bot_eq _

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
  -- Swap arguments via commutator_comm, then apply the iff:
  -- ⁅A, ⊤⁆ = ⊥ ↔ A ≤ centralizer ⊤
  have hCommBot' : ⁅A, (⊤ : Subgroup G)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]; exact hCommBot
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hCommBot'

end FeitThompson.BGsection1.P1_6

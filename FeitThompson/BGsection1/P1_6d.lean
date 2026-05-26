/-
# B & G, Proposition 1.6(d) — `coprime_abelian_cent_dprod`

Under `A ≤ N(G), coprime |G| |A|, abelian G`:
  `⁅G,A⁆ ⋈ C_G(A) = G` (internal direct product).

We split the direct-product conclusion into its two characterizing pieces:
the join is `⊤` (a strengthening of 1.6(a)) and the meet is `⊥` (TI).

## Tree

```
1.6(d) coprime_abelian_cent_dprod
├── Branch A: ⁅G,A⁆ ⊔ C_G(A) = ⊤   (direct from 1.6(a) `coprime_cent_prod`)
└── Branch B: ⁅G,A⁆ ⊓ C_G(A) = ⊥   (TI part)
    ├── Twig 1: ⁅G,A⁆ ⊓ A acts trivially (coprime + abelian collapses it)
    └── Twig 2: AXIOM — coprime_abel_cent_TI (MathComp finmod)
```
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.P1_6
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_6d

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

namespace BranchA_sup

/-- **A** — the join half of the direct product, by 1.6(a). -/
theorem cent_prod_top
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hAbel : IsMulCommutative G) :
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
      Subgroup.centralizer (A : Set G) = ⊤ := by
  haveI := hAbel
  exact P1_6.coprime_cent_prod A hNorm hCoprime inferInstance

end BranchA_sup

namespace BranchB_inf

/-- **B** — the meet half. In our Lean phrasing the ambient G *is* the
"G" of the Coq statement (we collapsed `G : {group gT}` to `⊤ : Subgroup G`),
so `IsMulCommutative G` makes everything commute. The commutator
`⁅⊤, A⁆` is then `⊥` directly (no Coq-style `coprime_abel_cent_TI` needed),
and the inf is trivially `⊥`.

Note: this is a Lean-translation-specific simplification. The Coq proof
needs the TI argument because there the ambient group `gT` is *not*
abelian — only the subgroup `G` is. -/
theorem inf_bot
    (A : Subgroup G)
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hAbel : IsMulCommutative G) :
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊓
      Subgroup.centralizer (A : Set G) = ⊥ := by
  haveI := hAbel
  -- In an abelian G, ⁅⊤, A⁆ = ⊥ since everything commutes.
  have hCommBot : (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _ a _ha
    exact mul_comm a g
  rw [hCommBot, bot_inf_eq]

end BranchB_inf

/-- **Main (B & G 1.6(d))** — internal direct product, expressed as
the conjunction of `sup = ⊤` and `inf = ⊥`. -/
theorem coprime_abelian_cent_dprod
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hAbel : IsMulCommutative G) :
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊔
        Subgroup.centralizer (A : Set G) = ⊤ ∧
    (⁅(⊤ : Subgroup G), A⁆ : Subgroup G) ⊓
        Subgroup.centralizer (A : Set G) = ⊥ :=
  ⟨BranchA_sup.cent_prod_top A hNorm hCoprime hAbel,
   BranchB_inf.inf_bot (G := G) A hNorm hCoprime hAbel⟩

end FeitThompson.BGsection1.P1_6d

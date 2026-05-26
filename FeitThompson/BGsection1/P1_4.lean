/-
# B & G, Proposition 1.4 — `coprime_trivg_cent_Fitting`

If A acts on G with coprime orders, G is solvable, and A's centralizer in
G is trivial, then A's centralizer in F(G) is trivial.

`A ⊆ N(G), coprime |G| |A|, solvable G, C_A(G) = 1 ⟹ C_A(F(G)) = 1`

## Tree (following B & G's proof)

```
coprime_trivg_cent_Fitting
├── Branch A: reduce to cyclic A    (wlog_cyclic)
│   ├── A1: every coprime regular action factors through cyclic subgroups
│   └── A2: trivial-centralizer property is hereditary on cyclic subgroups
├── Branch B: build the semidirect product X = G ⋊ A   (with cyclic A)
│   ├── B1: X is solvable
│   ├── B2: O_π(F(X)) ≤ A   where π = π(A)
│   └── B3: O_π(F(X)) = ⊥   (using regularity + C_A(G) = 1)
├── Branch C: F(X) ≤ G                (Fitting_in_normal)
│   ├── C1: F(X) is nilpotent
│   ├── C2: F(X)'s π-part is trivial (Branch B3)
│   └── C3: hence F(X) is a π'-group, and π'-Hall is G — Lagrange + structure
└── Branch D: conclude — C_A(F(G)) ⊆ C_A(F(X)) ⊆ C_A(X) ⊓ A = ⊥
```
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.P1_3
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace FeitThompson.BGsection1.P1_4

open FeitThompson.Stubs

variable {G : Type*} [Group G]

namespace BranchA

/-- **A1+A2**: it suffices to prove the statement for cyclic A.

Direct proof: if every cyclic `A' ≤ A` has `A' ⊓ centralizer F(G) = ⊥`,
then for any `x ∈ A ⊓ centralizer F(G)`, the cyclic subgroup `⟨x⟩ ≤ A`
also intersects `centralizer F(G)` trivially. Since `x ∈ ⟨x⟩`, this
forces `x = 1`. -/
theorem wlog_cyclic
    [Fintype G] (A : Subgroup G)
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hSol : IsSolvable G)
    (_hCentTrivial : A ⊓ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥)
    (hReduce : ∀ A' : Subgroup G, A' ≤ A → IsCyclic A' →
       A' ⊓ Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) = ⊥) :
    A ⊓ Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro x hx
  obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
  -- A' = ⟨x⟩ is cyclic, contained in A.
  let A' : Subgroup G := Subgroup.zpowers x
  have hA'le : A' ≤ A := Subgroup.zpowers_le.mpr hxA
  have hRed := hReduce A' hA'le inferInstance
  -- x ∈ A' ⊓ centralizer F(G), but that's ⊥, so x = 1.
  have hxA' : x ∈ A' := Subgroup.mem_zpowers x
  have hxBoth : x ∈ A' ⊓ Subgroup.centralizer
      ((FittingSubgroup G : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxA', hxC⟩
  rw [hRed] at hxBoth
  exact hxBoth

end BranchA

/-
**Branches B, C, D** of the tree (`semidirect_solvable`,
`piPart_Fitting_trivial`, `fitting_in_G`) were placeholder
`True`-returning theorems carrying no content. They captured the
intended Coq tree decomposition for documentation purposes but the
actual Lean proof shortcuts via `coprime_trivg_cent_Fitting_cyclic`
(the bundled axiom below). The placeholders were removed in Inc 24
since they cluttered the file without contributing soundness.

A future refactor that constructs the semidirect product `G ⋊ A` and
proves these intermediates as real theorems would re-introduce them
under their meaningful types.
-/

/-- **AXIOM**: cyclic case of P1.4 (Branches B + C + D assembled).

The full argument (BGsection1.v lines ~230-265) constructs the semidirect
product G ⋊ A, shows F(G ⋊ A) ≤ G, and applies the regularity hypothesis.
Deferred as a named axiom until we have semidirect-product machinery. -/
axiom coprime_trivg_cent_Fitting_cyclic
    {G : Type*} [Group G] [Fintype G] (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G)
    (hCentTrivial : A ⊓ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥)
    (hCyc : IsCyclic A) :
    A ⊓ Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) = ⊥

/-- **Main (B & G Proposition 1.4)**. -/
theorem coprime_trivg_cent_Fitting
    [Fintype G] (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G)
    (hCentTrivial : A ⊓ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥) :
    A ⊓ Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) = ⊥ := by
  apply BranchA.wlog_cyclic A hNorm hCoprime hSol hCentTrivial
  intro A' hA'le hA'cyc
  -- Cyclic-A' case: invoke the deferred axiom. The hypothesis transfers
  -- (A' inherits coprime + centralizer-triviality from A) are routine.
  refine coprime_trivg_cent_Fitting_cyclic A' (hA'le.trans hNorm) ?_ hSol ?_ hA'cyc
  · exact hCoprime.of_dvd dvd_rfl (Subgroup.card_dvd_of_le hA'le)
  · exact le_bot_iff.mp ((inf_le_inf_right _ hA'le).trans hCentTrivial.le)

end FeitThompson.BGsection1.P1_4

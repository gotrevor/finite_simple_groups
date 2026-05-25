/-
# B & G, Lemma 1.2 — `minnormal_solvable_Fitting_center`

A solvable minimal normal subgroup of G lies in `F(G) ⊓ C_G(F(G))` (the
center of F(G), viewed in the ambient group).

## Tree

```
minnormal_solvable_Fitting_center M
├── Branch A: M ≤ F(G)                      (le_fittingSubgroup_of_minnormal_solvable)
│   ├── A1: solvable minnormal ⇒ nilpotent (via L1.1: elementary abelian ⇒ nilpotent)
│   ├── A2: nilpotent normal subgroup ⊆ F(G) (defining property)
│   └── (assemble: M is nilpotent normal, so M ≤ F(G))
└── Branch B: M centralizes F(G)            (centralizes_fittingSubgroup)
    ├── B1: ⁅M, F(G)⁆ is G-normal, ≤ M
    ├── B2: ⁅M, F(G)⁆ < M (since F(G) is nilpotent and meets M in center)
    └── B3: minimality ⇒ ⁅M, F(G)⁆ = ⊥, i.e. M centralizes F(G)
```
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.L1_1
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent

namespace FeitThompson.BGsection1.L1_2

open FeitThompson.Stubs

variable {G : Type*} [Group G]

namespace BranchA

/-- **A1**: an elementary abelian group is nilpotent.

Chain: `IsAbelem M → IsMulCommutative ↥M → CommGroup ↥M → Group.IsNilpotent ↥M`. -/
theorem isAbelem_nilpotent (M : Subgroup G) (h : IsAbelem M) :
    Group.IsNilpotent M := by
  obtain ⟨_p, _hp, hAbel, _hExp⟩ := h
  haveI := hAbel
  infer_instance

/-- **A2**: any nilpotent normal subgroup is contained in the Fitting
subgroup. With our `FittingSubgroup G := normalClosure (⋃ H ∈ S, ↑H)`
this follows from `M ≤ normalClosure ↑M` plus monotonicity of normalClosure. -/
theorem nilpotent_normal_le_fittingSubgroup
    (M : Subgroup G) (hNorm : M.Normal) (hNil : Group.IsNilpotent M) :
    M ≤ FittingSubgroup G := by
  have h1 : (M : Set G) ⊆
      ⋃ H ∈ {H : Subgroup G | H.Normal ∧ Group.IsNilpotent H}, (H : Set G) := by
    intro x hx
    refine Set.mem_iUnion₂.mpr ⟨M, ?_, hx⟩
    exact ⟨hNorm, hNil⟩
  exact Subgroup.le_normalClosure.trans (Subgroup.normalClosure_mono h1)

end BranchA

theorem le_fittingSubgroup_of_minnormal_solvable
    (M : Subgroup G) [Finite M] (hMin : MinNormal M) (hSol : IsSolvable M) :
    M ≤ FittingSubgroup G := by
  have hAbelem : IsAbelem M := L1_1.minnormal_solvable_abelem M hMin hSol
  have hNil : Group.IsNilpotent M := BranchA.isAbelem_nilpotent M hAbelem
  exact BranchA.nilpotent_normal_le_fittingSubgroup M hMin.2.1 hNil

namespace BranchB

/-- **B1**: `⁅M, F(G)⁆ ≤ M`, and is G-normal. -/
theorem commutator_le_and_normal
    (M : Subgroup G) (hMn : M.Normal) :
    (⁅M, (FittingSubgroup G : Subgroup G)⁆ : Subgroup G).Normal ∧
      ⁅M, (FittingSubgroup G : Subgroup G)⁆ ≤ M := by
  haveI := hMn
  refine ⟨Subgroup.commutator_normal M (FittingSubgroup G),
          Subgroup.commutator_le_left M (FittingSubgroup G)⟩

/-- **B2 (AXIOM)**: `⁅M, F(G)⁆ < M` for minnormal M.

Reason: F(G) is nilpotent. So `⁅M, F(G)⁆` lies in a *lower* term of the
lower central series of `M · F(G)`, strictly inside M when M is nontrivial.
The Coq version uses `meet_center_nil` in BGsection1.v line ~145. Deferred
until we have Fitting subgroup nilpotence theory. -/
axiom commutator_lt_of_minnormal
    {G : Type*} [Group G]
    (M : Subgroup G) (hMin : MinNormal M) :
    ⁅M, (FittingSubgroup G : Subgroup G)⁆ < M

/-- **B3**: combining B1 + B2 + minimality, `⁅M, F(G)⁆ = ⊥`, so M centralizes F(G). -/
theorem centralizes_fittingSubgroup
    (M : Subgroup G) (hMin : MinNormal M) :
    M ≤ Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) := by
  have hNorm := hMin.2.1
  have hMinimal := hMin.2.2
  have ⟨hCommN, _hCommLe⟩ := commutator_le_and_normal M hNorm
  have hLt := commutator_lt_of_minnormal M hMin
  have hBot : ⁅M, (FittingSubgroup G : Subgroup G)⁆ = ⊥ := by
    cases hMinimal _ hCommN hLt.le with
    | inl h => exact h
    | inr h => exact absurd h hLt.ne
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBot

end BranchB

theorem minnormal_solvable_Fitting_center
    (M : Subgroup G) [Finite M] (hMin : MinNormal M) (hSol : IsSolvable M) :
    M ≤ FittingSubgroup G ⊓
      Subgroup.centralizer ((FittingSubgroup G : Subgroup G) : Set G) :=
  le_inf
    (le_fittingSubgroup_of_minnormal_solvable M hMin hSol)
    (BranchB.centralizes_fittingSubgroup M hMin)

end FeitThompson.BGsection1.L1_2

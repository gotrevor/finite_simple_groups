/-
# B & G, Lemma 1.1 — `minnormal_solvable_abelem`

Statement: a solvable minimal normal subgroup of a group is elementary abelian.

## Proof tree (branch → twig → leaf)

```
minnormal_solvable_abelem M hMin hSol
├── Branch A: M is abelian               (abelian_of_minnormal_solvable)
│   ├── Twig A1: ⁅M,M⁆ is characteristic in M, hence G-normal
│   ├── Twig A2: ⁅M,M⁆ < M for nontrivial solvable M
│   ├── Twig A3: minimality + (Twig A1) + (Twig A2) ⇒ ⁅M,M⁆ = ⊥
│   └── Twig A4: ⁅M,M⁆ = ⊥ ↔ M is abelian
└── Branch B: M has prime exponent       (prime_exp_of_minnormal_abelian)
    ├── Twig B1: For abelian M and prime p, the p-power image M^p is a
    │            characteristic subgroup, hence G-normal
    ├── Twig B2: By minimality, M^p ∈ {⊥, M}
    ├── Twig B3: If M^p = M for every prime p, M is trivial
    │            (a nontrivial finite group has some prime in its exponent)
    └── Twig B4: ∃ prime p, M^p = ⊥
```

Only the top-level structure matters. Leaves stay `sorry` for now — these
are the steps a mathematician writes as "hence" / "by Lagrange" / "clearly".
-/

import FeitThompson.MathlibStubs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.L1_1

open FeitThompson.Stubs

variable {G : Type*} [Group G]

-- ════════════════════════════════════════════════════════════════════
-- Branch A: M is abelian
-- ════════════════════════════════════════════════════════════════════

namespace BranchA

/-- **Twig A1**: For any G-normal subgroup M, `⁅M,M⁆` is G-normal.
Mathlib provides `Subgroup.commutator_normal` as an instance. -/
theorem commutator_self_normal_of_normal (M : Subgroup G) (hM : M.Normal) :
    (⁅M, M⁆ : Subgroup G).Normal := by
  haveI := hM
  exact Subgroup.commutator_normal M M

/-- **Twig A2**: A nontrivial solvable subgroup has proper commutator subgroup.

Mirrors mathlib's `IsSolvable.commutator_lt_of_ne_bot` but with `IsSolvable ↥M`
instead of `IsSolvable G` (we don't need the ambient group to be solvable). -/
theorem commutator_lt_self (M : Subgroup G) (hSol : IsSolvable M) (hNT : M ≠ ⊥) :
    ⁅M, M⁆ < M := by
  haveI := hSol
  haveI : Nontrivial ↥M := M.nontrivial_iff_ne_bot.mpr hNT
  have h : _root_.commutator ↥M < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial ↥M
  rw [← M.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
  exact h

/-- **Twig A3**: Apply minimality of M to ⁅M,M⁆.

The proper inclusion (Twig A2) plus G-normality of ⁅M,M⁆ (Twig A1) plus
`MinNormal M` forces ⁅M,M⁆ = ⊥. -/
theorem commutator_eq_bot
    (M : Subgroup G) (hMin : MinNormal M) (hSol : IsSolvable M) :
    (⁅M, M⁆ : Subgroup G) = ⊥ := by
  obtain ⟨hNT, hNorm, hMinimal⟩ := hMin
  have hLt : ⁅M, M⁆ < M := commutator_lt_self M hSol hNT
  have hCommN : (⁅M, M⁆ : Subgroup G).Normal :=
    commutator_self_normal_of_normal M hNorm
  -- minimality: any G-normal K ≤ M is ⊥ or M
  cases hMinimal ⁅M, M⁆ hCommN hLt.le with
  | inl h => exact h
  | inr h => exact absurd h hLt.ne

/-- **Twig A4**: `⁅M, M⁆ = ⊥` iff M is abelian.

Composes two mathlib lemmas:
  - `Subgroup.commutator_eq_bot_iff_le_centralizer : ⁅H₁,H₂⁆ = ⊥ ↔ H₁ ≤ centralizer H₂`
  - `Subgroup.le_centralizer_iff_isMulCommutative : K ≤ centralizer K ↔ IsMulCommutative K`
-/
theorem isMulCommutative_of_commutator_eq_bot
    (M : Subgroup G) (h : (⁅M, M⁆ : Subgroup G) = ⊥) :
    IsMulCommutative M :=
  Subgroup.le_centralizer_iff_isMulCommutative.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)

end BranchA

/-- **Branch A** assembled: a minimal G-normal solvable subgroup is abelian. -/
theorem abelian_of_minnormal_solvable
    (M : Subgroup G) (hMin : MinNormal M) (hSol : IsSolvable M) :
    IsMulCommutative M := by
  exact BranchA.isMulCommutative_of_commutator_eq_bot M
    (BranchA.commutator_eq_bot M hMin hSol)

-- ════════════════════════════════════════════════════════════════════
-- Branch B: M has prime exponent (given that M is abelian)
-- ════════════════════════════════════════════════════════════════════

namespace BranchB

/-- p-th power image of a subgroup. For abelian M this is a subgroup. -/
def pPowerImage (M : Subgroup G) (p : ℕ) : Set G := { x | ∃ m ∈ M, m ^ p = x }

/-- **Twig B1**: For abelian M, `pPowerImage M p` is a characteristic subgroup
of M, hence G-normal when M is. -/
theorem pPowerImage_isSubgroup_and_normal
    (M : Subgroup G) (_hAbel : IsMulCommutative M) (_hNorm : M.Normal) (p : ℕ) :
    ∃ K : Subgroup G, (K : Set G) = pPowerImage M p ∧ K.Normal ∧ K ≤ M := by
  sorry

/-- **Twig B2**: by minimality, `pPowerImage M p` is ⊥ or M. -/
theorem pPowerImage_bot_or_top
    (M : Subgroup G) (hMin : MinNormal M) (hAbel : IsMulCommutative M) (p : ℕ) :
    ∃ K : Subgroup G, (K : Set G) = pPowerImage M p ∧ (K = ⊥ ∨ K = M) := by
  obtain ⟨_, hNorm, hMinimal⟩ := hMin
  obtain ⟨K, hK, hKn, hKle⟩ := pPowerImage_isSubgroup_and_normal M hAbel hNorm p
  exact ⟨K, hK, hMinimal K hKn hKle⟩

/-- **Twig B3**: if M is nontrivial finite, there's *some* prime p for which
the p-power map is not surjective on M. (Otherwise the exponent of M would
be divisible by every prime, impossible for finite |M| > 1.) -/
theorem exists_prime_pPowerImage_ne_top
    (M : Subgroup G) [Finite M] (_hNT : M ≠ ⊥) (_hAbel : IsMulCommutative M) :
    ∃ p : ℕ, p.Prime ∧
      ∀ K : Subgroup G, (K : Set G) = pPowerImage M p → K ≠ M := by
  sorry

/-- **Twig B4**: combining B2 and B3 — there is a prime p with `M^p = ⊥`,
equivalently every m ∈ M satisfies `m^p = 1`. -/
theorem exists_prime_exp
    (M : Subgroup G) [Finite M] (hMin : MinNormal M) (hAbel : IsMulCommutative M) :
    ∃ p : ℕ, p.Prime ∧ ∀ m ∈ M, m ^ p = 1 := by
  have hNT : M ≠ ⊥ := hMin.1
  obtain ⟨p, hp, hNotTop⟩ := exists_prime_pPowerImage_ne_top M hNT hAbel
  obtain ⟨K, hKeq, hKalt⟩ := pPowerImage_bot_or_top M hMin hAbel p
  -- K is the p-power image; either ⊥ or M; not M (by hNotTop); so ⊥.
  have hKbot : K = ⊥ := by
    cases hKalt with
    | inl h => exact h
    | inr h => exact absurd h (hNotTop K hKeq)
  refine ⟨p, hp, ?_⟩
  intro m hm
  -- m^p ∈ pPowerImage M p (witnessed by m)
  have hMemSet : m ^ p ∈ pPowerImage M p := ⟨m, hm, rfl⟩
  rw [← hKeq] at hMemSet
  -- hMemSet : m^p ∈ (K : Set G) is the same as m^p ∈ K (SetLike coe)
  have hMemK : m ^ p ∈ K := hMemSet
  rw [hKbot] at hMemK
  exact Subgroup.mem_bot.mp hMemK

end BranchB

/-- **Branch B** assembled: a minimal G-normal abelian subgroup has prime
exponent. -/
theorem prime_exp_of_minnormal_abelian
    (M : Subgroup G) [Finite M] (hMin : MinNormal M) (hAbel : IsMulCommutative M) :
    ∃ p : ℕ, p.Prime ∧ ∀ m ∈ M, m ^ p = 1 :=
  BranchB.exists_prime_exp M hMin hAbel

-- ════════════════════════════════════════════════════════════════════
-- Top-level: assemble Branch A and Branch B
-- ════════════════════════════════════════════════════════════════════

/-- **Main theorem (B & G Lemma 1.1, first part)**.

A solvable minimal G-normal subgroup is elementary abelian. -/
theorem minnormal_solvable_abelem
    (M : Subgroup G) [Finite M] (hMin : MinNormal M) (hSol : IsSolvable M) :
    IsAbelem M := by
  -- Branch A: M is abelian
  have hAbel : IsMulCommutative M := abelian_of_minnormal_solvable M hMin hSol
  -- Branch B: M has prime exponent
  obtain ⟨p, hp, hExp⟩ := prime_exp_of_minnormal_abelian M hMin hAbel
  -- Assemble into IsAbelem
  -- IsAbelem M needs: ∃ p prime, IsMulCommutative M ∧ ∀ g, g^p = 1
  refine ⟨p, hp, hAbel, ?_⟩
  intro g
  apply Subtype.ext
  push_cast
  exact hExp g.val g.property

end FeitThompson.BGsection1.L1_1

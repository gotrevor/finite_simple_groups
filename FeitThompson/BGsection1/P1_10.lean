/-
# B & G, Proposition 1.10 — `coprime_nil_faithful_cent_stab`

For nilpotent G with `A ≤ N(G)`, `coprime |G| |A|`, let `C := C_G(A)`.
If `C_G(C) ≤ C` then `A ≤ C(G)`.

The hypothesis `C_G(C) ≤ C` is the "self-centralizing" condition on the
fixed-point subgroup. Combined with nilpotency it forces the action on G
to be trivial via the normalizer-of-normalizer argument.

## Tree (Inc 27 — soundness fix)

```
1.10 coprime_nil_faithful_cent_stab
├── A ≤ C(C) by centralization symmetric              — proved inline
├── ⁅N_G(C), A⁆ ≤ C                                   — AXIOM (Coq line 422-425)
│       (comm_norm_cent_cent + intersection-normalize + hSelfCent)
├── C is N-conjugation-stable                          — definitional (N = normalizer C)
├── Apply relativized stable_factor_cent at K = N      — uses 1.9-base'
│   ⟹ A ≤ C(N)
├── Hence N ≤ C(A) = C, so N = C                      — proved inline
└── C.normalizer = C + nilpotent G ⟹ C = ⊤            — mathlib NormalizerCondition
    ⟹ A ≤ C(⊤)
```

## What changed from Inc 16

The previous version had a false-claim `stable_factor_data` axiom that
asserted `(centralizer A).Normal` (in G) without `A.Normal` — this is
not true in general. The hSelfCent hypothesis was unused. Inc 27 fixes
this by tracking `N := N_G(C)` (where C is K-normal by definition of
normalizer) and collapsing N = ⊤ at the end via mathlib's
`normalizerCondition_of_isNilpotent`. The hSelfCent hypothesis is now
load-bearing — it's what makes the `⁅N, A⁆ ≤ C` axiom statement
mathematically true (the underlying Coq proof uses it via `comm_norm_cent_cent`
+ intersection normalization).

Net axiom count: ±0. One false axiom (`stable_factor_data`) removed,
one cited axiom (`comm_norm_cent_subset_cent`) added.
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.P1_9_base
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent

namespace FeitThompson.BGsection1.P1_10

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

namespace BranchA_comm

/-- **AXIOM** — Coq's `comm_norm_cent_cent` + intersection-normalize chain
applied at the (N_G(C), A, C) instantiation needed by P1_10.

Coq: BGsection1.v:422-425. Concretely, `comm_norm_cent_cent`
(math-comp `solvable/commutator.v:293`) gives `⁅N_G(C), A⁆ ⊆ C(C)`
under: A normalizes N_G(C) (derived from A self-conjugates A so it
fixes C = C(A), hence fixes N_G(C)), A ⊆ C(C) (centralization
symmetric since C = C(A)), and N_G(C) ⊆ N(C) (definitional). The
`hSelfCent` hypothesis then collapses `C(C) ∩ G = C_G(C) ⊆ C` to
give the final `⁅N_G(C), A⁆ ≤ C`.

A future increment could inline-prove this by adding `comm_norm_cent_cent`
to `CommutatorExtras` (mathlib gap, ~50 LOC mirror of MathComp). For now
the entire chain is one cited axiom. -/
axiom comm_norm_cent_subset_cent
    {G : Type*} [Group G] [Fintype G]
    (A : Subgroup G)
    (_hSelfCent : Subgroup.centralizer
        ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G)
      ≤ Subgroup.centralizer (A : Set G)) :
    (⁅Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G),
       A⁆ : Subgroup G)
      ≤ Subgroup.centralizer (A : Set G)

end BranchA_comm

/-- **Main (B & G 1.10)** — `coprime_nil_faithful_cent_stab`.

The `hNorm : A ≤ N(⊤)` hypothesis matches Coq's `A ⊆ N(G)` but is
vacuous in Lean's framing (where ⊤ is the whole group). We carry it
for signature compatibility. -/
theorem coprime_nil_faithful_cent_stab
    (A : Subgroup G)
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hNil : Group.IsNilpotent G)
    (hSelfCent : Subgroup.centralizer
        ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G)
      ≤ Subgroup.centralizer (A : Set G)) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  -- Local abbreviations for clarity.
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let N : Subgroup G := Subgroup.normalizer (C : Set G)
  -- A ≤ C(C) — centralization symmetric: C = C(A) means every c ∈ C
  -- commutes with every a ∈ A, so every a ∈ A commutes with every c ∈ C.
  have hACC : A ≤ Subgroup.centralizer (C : Set G) := by
    intro a ha b hb
    have hbA : b ∈ Subgroup.centralizer (A : Set G) := hb
    exact (hbA a ha).symm
  -- C ≤ N — every subgroup is contained in its normalizer.
  have hCN : C ≤ N := Subgroup.le_normalizer
  -- ⁅N, A⁆ ≤ C — from the cited axiom (Coq line 422-425).
  have hCommNC : (⁅N, A⁆ : Subgroup G) ≤ C :=
    BranchA_comm.comm_norm_cent_subset_cent A hSelfCent
  -- C is N-conjugation-stable — by definition of normalizer.
  have hConjStable : ∀ k ∈ N, ∀ h ∈ C, k * h * k⁻¹ ∈ C := by
    intro k hk h hh
    exact (Subgroup.mem_normalizer_iff.mp hk h).mp hh
  -- Assemble IsStableFactor' A N C.
  have hStable' : P1_9_base.IsStableFactor' A N C :=
    { le_K := hCN
      comm_le := hCommNC
      conjStable := hConjStable }
  -- Nilpotent ⟹ solvable.
  haveI : IsSolvable G := haveI := hNil; IsNilpotent.to_isSolvable
  -- coprime |N| |A| from coprime |G| |A| via N ≤ ⊤.
  have hCoprimeN : (Nat.card N).Coprime (Nat.card A) := by
    have hNdvd : Nat.card N ∣ Nat.card G := by
      have h1 : Nat.card N ∣ Nat.card (⊤ : Subgroup G) :=
        Subgroup.card_dvd_of_le le_top
      rwa [Subgroup.card_top] at h1
    exact hCoprime.of_dvd_left hNdvd
  -- IsSolvable N from IsSolvable G.
  haveI : IsSolvable N := inferInstance
  -- Apply relativized 1.9-base at K = N.
  have hACN : A ≤ Subgroup.centralizer (N : Set G) :=
    P1_9_base.BranchChain.stable_factor_cent_chain' A N C
      hStable' hACC hCoprimeN inferInstance
  -- N ≤ C: from A ≤ C(N), centralization symmetric.
  have hNC : N ≤ C := by
    intro n hn a ha
    have h2 : a ∈ Subgroup.centralizer (N : Set G) := hACN ha
    exact (h2 n hn).symm
  -- N = C, hence C is self-normalizing.
  have hSelfNorm : N = C := le_antisymm hNC hCN
  -- Nilpotent G + NormalizerCondition ⟹ C = ⊤.
  haveI : Group.IsNilpotent G := hNil
  have hCond : NormalizerCondition G := normalizerCondition_of_isNilpotent
  have hC_top : C = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hCond) C hSelfNorm
  -- A ≤ C(C) and C = ⊤ ⟹ A ≤ C(⊤).
  rw [show (⊤ : Subgroup G) = C from hC_top.symm]
  exact hACC

end FeitThompson.BGsection1.P1_10

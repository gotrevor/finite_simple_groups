/-
# B & G, Proposition 1.9 — `stable_series_cent`

If G has an A-stable series ending at `G` (i.e. a chain of A-stable factors
from `⊥` to `G`), with `coprime |G| |A|` and `G` solvable, then A acts
trivially on G.

Proof: induction on the length of the series, applying the base case
(`P1_9_base.stable_factor_cent`) at each step.

## Tree

```
1.9 stable_series_cent
└── Branch: induction on series length
    ├── Base: series = [⊥], so G = ⊥; A trivial on ⊥ vacuously
    └── Step: peel off last factor H ⊲ G; A trivial on H (by IH);
              apply 1.9 base case to (G, H) ⇒ A trivial on G
```
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.P1_9_base
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Solvable

namespace FeitThompson.BGsection1.P1_9

open FeitThompson.Stubs FeitThompson.BGsection1.P1_9_base

variable {G : Type*} [Group G] [Fintype G]

/-- `IsAStableFactor A Hi Hj` says `(Hi, Hj)` is an A-stable factor pair:
`Hi ≤ Hj`, `⁅Hj, A⁆ ≤ Hi`, and `Hi` is closed under `Hj`-conjugation.

The conjugation-stability clause is the per-pair analog of "Hi ⊲ Hj in
the ambient G," matching MathComp's `stable_factor` predicate. **Inc 31**
adds this clause — the prior definition omitted it, which made
`series_cent_of_stable` an unprovable list induction (the base case
`stable_factor_cent_chain'` requires `conjStable` per step). -/
def IsAStableFactor (A : Subgroup G) (Hi Hj : Subgroup G) : Prop :=
  Hi ≤ Hj ∧ (⁅Hj, A⁆ : Subgroup G) ≤ Hi ∧
    ∀ k ∈ Hj, ∀ h ∈ Hi, k * h * k⁻¹ ∈ Hi

/-- `IsAStableSeries A s` says `s : List (Subgroup G)` is an A-stable series:
`s = [⊥, H₁, H₂, …, ⊤]` with each consecutive pair `(Hᵢ, Hᵢ₊₁)` an
A-stable factor (`IsAStableFactor A Hᵢ Hᵢ₊₁`).

**Inc 31:** refactored to `List.IsChain` over `IsAStableFactor` (was an
indexed `∀ i ∃ Hi Hj, s[i]? = some Hi ∧ ...`). The chain form makes
list induction natural and matches mathlib's standard "consecutive pairs
satisfy R" idiom. -/
def IsAStableSeries (A : Subgroup G) (s : List (Subgroup G)) : Prop :=
  s.head? = some ⊥ ∧ s.getLast? = some ⊤ ∧
    s.IsChain (IsAStableFactor A)

namespace Branch_induct

/-- Helper for the list induction: if A acts trivially on the head `H` of a
chain `H :: rest` and the chain is stable, then A acts trivially on the
last element of the chain.

Proceeds by induction on `rest`. Each step peels the next factor and
applies `stable_factor_cent_chain'` (Inc 26's relativized 1.9-base).
Subgroup-solvability auto-derives via `subgroup_solvable_of_solvable`. -/
private theorem cent_of_chain
    (A : Subgroup G) (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    ∀ (H : Subgroup G) (rest : List (Subgroup G))
      (_hChain : (H :: rest).IsChain (IsAStableFactor A))
      (_hCent : A ≤ Subgroup.centralizer (H : Set G)),
        A ≤ Subgroup.centralizer
          (((H :: rest).getLast (List.cons_ne_nil _ _)) : Set G)
  | H, [], _hChain, hCent => by simpa using hCent
  | H, Hnext :: tail, hChain, hCent => by
    haveI := hSol
    -- Extract the (H, Hnext) factor + the tail chain.
    rw [List.isChain_cons_cons] at hChain
    obtain ⟨hFactor, hTailChain⟩ := hChain
    obtain ⟨hHle, hCommLe, hConjStab⟩ := hFactor
    -- Apply Inc 26's stable_factor_cent_chain' at K = Hnext, H = H.
    have hStable' : P1_9_base.IsStableFactor' A Hnext H :=
      { le_K := hHle
        comm_le := hCommLe
        conjStable := hConjStab }
    -- Derive coprime |Hnext| |A| via Lagrange.
    have hCoprime' : (Nat.card Hnext).Coprime (Nat.card A) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card Hnext) hCoprime
    -- Subgroups of solvable groups are solvable (auto-instance).
    have hCentNext : A ≤ Subgroup.centralizer (Hnext : Set G) :=
      P1_9_base.BranchChain.stable_factor_cent_chain' A Hnext H
        hStable' hCent hCoprime' inferInstance
    -- Recurse on the tail with H := Hnext.
    have := cent_of_chain A hCoprime hSol Hnext tail hTailChain hCentNext
    simpa using this

/-- Discharged: `series_cent_of_stable` is now a real theorem rather than
an axiom. Proof iterates `stable_factor_cent_chain'` along the series via
the `cent_of_chain` helper.

The series's head is `⊥`, and `A ≤ centralizer(⊥) = ⊤` is trivial (every
element commutes with `1`), so we seed the induction at `H := ⊥`. The
series's last element is `⊤`, so the conclusion gives `A ≤ centralizer(⊤)`. -/
theorem series_cent_of_stable
    (A : Subgroup G) (s : List (Subgroup G))
    (hStable : IsAStableSeries A s)
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  obtain ⟨hHead, hLast, hChain⟩ := hStable
  -- The series has at least one element (head = ⊥), so destruct.
  match hs : s, hHead, hLast, hChain with
  | [], hHead, _, _ => simp at hHead
  | H :: rest, hHead, hLast, hChain =>
    -- H = ⊥ from hHead.
    have hHeq : H = (⊥ : Subgroup G) := by simpa using hHead
    -- Last element = ⊤ from hLast.
    have hLastEq : (H :: rest).getLast (List.cons_ne_nil _ _) = (⊤ : Subgroup G) := by
      have := hLast
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at this
      exact Option.some_injective _ this
    -- Seed: A ≤ centralizer(⊥) = ⊤ trivially.
    have hCentBot : A ≤ Subgroup.centralizer (H : Set G) := by
      subst hHeq
      intro a _ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hb
      subst hb
      group
    -- Apply the chain lemma, then rewrite the last element to ⊤.
    have := cent_of_chain A hCoprime hSol H rest hChain hCentBot
    rw [hLastEq] at this
    exact this

end Branch_induct

/-- **Main (B & G 1.9)** — `stable_series_cent`. -/
theorem stable_series_cent
    (A : Subgroup G) (s : List (Subgroup G))
    (hStable : IsAStableSeries A s)
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hSol : IsSolvable G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) :=
  Branch_induct.series_cent_of_stable A s hStable hCoprime hSol

end FeitThompson.BGsection1.P1_9

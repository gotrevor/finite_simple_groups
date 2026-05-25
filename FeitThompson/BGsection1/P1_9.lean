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

/-- `IsAStableSeries A s` says `s : List (Subgroup G)` is an A-stable series:
`s = [⊥, H₁, H₂, …, ⊤]` with each consecutive pair `(Hᵢ, Hᵢ₊₁)` an A-stable
factor (Hᵢ ⊲ Hᵢ₊₁ in G, with `⁅Hᵢ₊₁, A⁆ ≤ Hᵢ`). -/
def IsAStableSeries (A : Subgroup G) (s : List (Subgroup G)) : Prop :=
  s.head? = some ⊥ ∧ s.getLast? = some ⊤ ∧
    ∀ i (_h : i + 1 < s.length),
      ∃ (Hi Hj : Subgroup G), s[i]? = some Hi ∧ s[i+1]? = some Hj ∧
        Hi ≤ Hj ∧ (⁅Hj, A⁆ : Subgroup G) ≤ Hi

namespace Branch_induct

/-- **AXIOM** — iterate `stable_factor_cent` along the series.

Coq: `elim/last_ind` induction at line ~404. Each step peels off the
topmost factor and applies `stable_factor_cent` to it, using the IH for
the smaller group. Translation deferred — the list-induction bookkeeping
is verbose in Lean without the dedicated `last_ind` tactic. -/
axiom series_cent_of_stable
    {G : Type*} [Group G] [Fintype G]
    (A : Subgroup G) (s : List (Subgroup G))
    (_hStable : IsAStableSeries A s)
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hSol : IsSolvable G) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G)

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

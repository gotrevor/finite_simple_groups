/-
# B & G, Theorem 1.11 — `coprime_odd_faithful_Ohm1`

For a p-group G of odd order, with A normalizing G and `coprime |G| |A|`,
faithful action of A on `Ω₁(G)` implies faithful action on G.

Stronger than 1.6(e) (which assumes G abelian). The Coq proof goes via
Aschbacher 24.7 (`abelian_charsimple_special`).

## Tree

```
1.11 coprime_odd_faithful_Ohm1
├── Branch A: trivial G case (G = ⊥)        — proved
└── Branch B: nontrivial G case               — AXIOM (`nontrivial_assembly`)
    Bundled as one cited axiom; would conceptually decompose into:
      B1: wlog ⁅⊤, A⁆ = ⊤  (via 1.6(a), 1.6(b))
      B2: abelian_charsimple_special ⇒ Ω₁(G) = Z(G)
      B3: A ≤ C(Z(G)) lifts to A ≤ C(G) in p-special G
    A future refactor that splits the assembly into B1+B2+B3 will need
    to re-introduce the corresponding axiom statements.
```
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.P1_6
import FeitThompson.BGsection1.P1_6e
import FeitThompson.BGsection1.P1_8
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup

namespace FeitThompson.BGsection1.T1_11

open FeitThompson.Stubs FeitThompson.BGsection1.P1_6e

variable {G : Type*} [Group G] [Fintype G]

namespace BranchA_trivial

/-- **A** — if G is the trivial group, A centralizes G vacuously. -/
theorem trivial_case (A : Subgroup G) (hG : (⊤ : Subgroup G) = ⊥) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  intro a _ b hb
  have hb' : b ∈ (⊥ : Subgroup G) := hG ▸ hb
  have : b = 1 := Subgroup.mem_bot.mp hb'
  simp [this]

end BranchA_trivial

namespace BranchB_nontrivial

/-- **B-assembly (AXIOM)** — nontrivial-case assembly.

Coq: BGsection1.v lines ~454-465. The "structure follows from B2"
collapse: A centralizes Z(G) = Ω₁(G), and the Frattini-style argument
extends to all of G.

Decomposes into: B1 (wlog), B2 (charsimple), and B3 (center lift). -/
axiom nontrivial_assembly
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) (A : Subgroup G)
    (_hG : IsPGroup p (⊤ : Subgroup G))
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hOdd : Odd (Nat.card G))
    (_hFaith : A ≤ Subgroup.centralizer ((Ohm1 G : Subgroup G) : Set G))
    (_hNT : (⊤ : Subgroup G) ≠ ⊥) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G)

end BranchB_nontrivial

/-- **Main (B & G 1.11)** — `coprime_odd_faithful_Ohm1`. -/
theorem coprime_odd_faithful_Ohm1
    (p : ℕ) (A : Subgroup G)
    (hG : IsPGroup p (⊤ : Subgroup G))
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hOdd : Odd (Nat.card G))
    (hFaith : A ≤ Subgroup.centralizer ((Ohm1 G : Subgroup G) : Set G)) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  by_cases hTriv : (⊤ : Subgroup G) = ⊥
  · exact BranchA_trivial.trivial_case A hTriv
  · exact BranchB_nontrivial.nontrivial_assembly p A hG hNorm hCoprime hOdd hFaith hTriv

end FeitThompson.BGsection1.T1_11

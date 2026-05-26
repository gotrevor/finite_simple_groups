/-
# B & G, Corollary 1.12 — `coprime_odd_faithful_cent_abelem`

For an elementary abelian p-subgroup `E` of an odd-order p-group `G` with
`A` normalizing `G` and `coprime |G| |A|`, if `A` centralizes the
p-torsion of `C_G(E)`, then A centralizes G.

Direct corollary of 1.11: apply Ohm1-faithfulness to the centralizer of E.

## Tree

```
1.12 coprime_odd_faithful_cent_abelem
├── Branch A: trivial G case  — proved
└── Branch B: nontrivial G case
    ├── B1: AXIOM — A ⊆ C(Ω₁(C_G(E)))  (Coq `OhmE` + `cent_gen`)
    ├── B2: nilpotent of p-group  (mathlib `IsPGroup.isNilpotent`)
    ├── B3: AXIOM — apply 1.10 (coprime_nil_faithful_cent_stab) with C_G(E)
    └── B4: assemble via 1.11 on C_G(E)
```

The actual Coq proof routes through 1.11 *and* 1.10. We axiomatize the
chain since each step requires non-trivial mathlib bricks (`OhmE`,
`cent_gen`, plus the `Ldiv_p` operator).
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.T1_11
import FeitThompson.BGsection1.P1_10
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PGroup

namespace FeitThompson.BGsection1.C1_12

open FeitThompson.Stubs FeitThompson.BGsection1.P1_6e

variable {G : Type*} [Group G] [Fintype G]

/-- `Ldiv_p p H` — the set of p-torsion elements of H. MathComp `'Ldiv_p`.
Stubbed as `Ohm1 H` since both capture "elements of order dividing p"
in our finite p-group setting. -/
noncomputable def Ldiv_p (_p : ℕ) (H : Subgroup G) : Subgroup G := Ohm1 ↥H |>.map H.subtype

namespace BranchB_nontrivial

/-- **B (AXIOM)** — the corollary's main content.

Coq: `coprime_odd_faithful_cent_abelem` proof at BGsection1.v lines
~472-487. Translation gates on:
- `OhmE` for `C_G(E)` (Ohm-of-centralizer-of-abelem)
- `cent_gen` (centralizer of a generating set = centralizer of the set)
- Application of 1.11 (`coprime_odd_faithful_Ohm1`) to `C_G(E)`
- Application of 1.10 (`coprime_nil_faithful_cent_stab`) to lift back to G

All of these are tractable; we package the chain as one cited axiom. -/
axiom corollary_assembly
    {G : Type*} [Group G] [Fintype G]
    (p : ℕ) (A E : Subgroup G)
    (_hE_le_G : E ≤ ⊤)
    (_hE_abelem : IsAbelem E)
    (_hG : IsPGroup p (⊤ : Subgroup G))
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hOdd : Odd (Nat.card G))
    (_hFaith : A ≤ Subgroup.centralizer
        ((Ldiv_p p (Subgroup.centralizer (E : Set G)) : Subgroup G) : Set G)) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G)

end BranchB_nontrivial

/-- **Main (B & G 1.12)** — `coprime_odd_faithful_cent_abelem`. -/
theorem coprime_odd_faithful_cent_abelem
    (p : ℕ) (A E : Subgroup G)
    (hE_le_G : E ≤ ⊤)
    (hE_abelem : IsAbelem E)
    (hG : IsPGroup p (⊤ : Subgroup G))
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hOdd : Odd (Nat.card G))
    (hFaith : A ≤ Subgroup.centralizer
        ((Ldiv_p p (Subgroup.centralizer (E : Set G)) : Subgroup G) : Set G)) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  by_cases hTriv : (⊤ : Subgroup G) = ⊥
  · -- G trivial: same vacuous argument as T1_11.
    intro a _ b hb
    have hb' : b ∈ (⊥ : Subgroup G) := hTriv ▸ hb
    have : b = 1 := Subgroup.mem_bot.mp hb'
    simp [this]
  · exact BranchB_nontrivial.corollary_assembly p A E hE_le_G hE_abelem hG hNorm
      hCoprime hOdd hFaith

end FeitThompson.BGsection1.C1_12

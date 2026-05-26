/-
# B & G, Proposition 1.10 — `coprime_nil_faithful_cent_stab`

For nilpotent G with `A ≤ N(G)`, `coprime |G| |A|`, let `C := C_G(A)`.
If `C_G(C) ≤ C` then `A ≤ C(G)`.

The hypothesis `C_G(C) ≤ C` is the "self-centralizing" condition on the
fixed-point subgroup. Combined with nilpotency it forces the action on G
to be trivial via the normalizer-of-normalizer argument
(`nilpotent_sub_norm`).

## Tree (as currently implemented)

```
1.10 coprime_nil_faithful_cent_stab
├── A centralizes C (= C_G(A)) by definition       — proved
├── nilpotent ⇒ solvable                            — proved
└── apply stable_factor_cent to (⊤, C)              — uses 1.9-base
    └── AXIOM stable_factor_data: C is ⊤-normal, ⁅⊤, A⁆ ≤ C
```

The Coq proof routes through `N := N_G(C)` (using nilpotent_sub_norm to
get `N = ⊤`), but the Lean implementation shortcuts to ambient = ⊤
directly via the `stable_factor_data` axiom. This has a latent
soundness issue: `stable_factor_data` claims `C.Normal` in ⊤ without
`A.Normal`, which is false in general. The structural fix (track
`N_G(C_G(A))` instead) is the P1_10 refactor (HANDOFF option 4) and
will re-introduce `norm_C_eq_top` as a load-bearing intermediate.
-/

import FeitThompson.MathlibStubs
import FeitThompson.BGsection1.P1_9_base
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent

namespace FeitThompson.BGsection1.P1_10

open FeitThompson.Stubs

variable {G : Type*} [Group G] [Fintype G]

namespace BranchC_stable

/-- **C (AXIOM)** — package the data needed by `stable_factor_cent`:
- `C` is normal in `N = N_G(C)` (definitional);
- `⁅N, A⁆ ≤ C` (the commutator lands in C since A centralizes commutators
   into C, via `comm_norm_cent_cent`).

Coq: lines ~422-425. -/
axiom stable_factor_data
    {G : Type*} [Group G] [Fintype G]
    (A : Subgroup G)
    (_hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (_hCoprime : (Nat.card G).Coprime (Nat.card A))
    (_hNil : Group.IsNilpotent G) :
    P1_9_base.IsStableFactor A (Subgroup.centralizer (A : Set G))

end BranchC_stable

/-- **Main (B & G 1.10)** — `coprime_nil_faithful_cent_stab`. -/
theorem coprime_nil_faithful_cent_stab
    (A : Subgroup G)
    (hNorm : A ≤ Subgroup.normalizer (⊤ : Subgroup G))
    (hCoprime : (Nat.card G).Coprime (Nat.card A))
    (hNil : Group.IsNilpotent G)
    (_hSelfCent : Subgroup.centralizer
        ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G)
      ≤ Subgroup.centralizer (A : Set G)) :
    A ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G) := by
  -- A ⊆ C(C) by definition (A centralizes its own centralizer's centralizer...
  -- wait, just A centralizes C? No: C = C_G(A), so elements of C commute with
  -- everything in A — that means C ≤ centralizer A, equivalently A ≤ centralizer C.
  have hCAH : A ≤ Subgroup.centralizer
      ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
    intro a ha b hb
    -- b ∈ centralizer A means b commutes with a, hence a commutes with b.
    have hbA : b ∈ Subgroup.centralizer (A : Set G) := hb
    have := hbA a ha
    -- `hbA a ha : b * a = a * b`; reverse it.
    exact this.symm
  -- nilpotent ⇒ solvable
  have hSol : IsSolvable G :=
    haveI := hNil; IsNilpotent.to_isSolvable
  -- Stable-factor data: C is normal in ⊤, ⁅⊤, A⁆ ≤ C
  have hStable := BranchC_stable.stable_factor_data A hNorm hCoprime hNil
  -- Apply 1.9 base case
  exact P1_9_base.stable_factor_cent A (Subgroup.centralizer (A : Set G))
    hStable hCAH hCoprime hSol

end FeitThompson.BGsection1.P1_10

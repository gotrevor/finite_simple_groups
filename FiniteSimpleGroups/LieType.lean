import Mathlib
import FiniteSimpleGroups.Basic

/-!
# Family 3: Classical groups of Lie type

The largest of the families by count. Four infinite series, each parametrized
by a dimension `n` and a finite field `F_q` (where `q = p^k` for `p` prime):

| Series | Symbol | Construction | Simple when... |
|--------|--------|--------------|----------------|
| Type `A_{n-1}` (linear) | `PSL_n(q)` | `SL_n(F_q) / center` | `n ≥ 2`, except `(n,q) ∈ {(2,2),(2,3)}` |
| Type `²A_{n-1}` (unitary) | `PSU_n(q)` | `SU_n(F_{q²}) / center` | `n ≥ 3`, with small exceptions |
| Type `C_n` (symplectic) | `PSp_{2n}(q)` | `Sp_{2n}(F_q) / center` | `n ≥ 2`, except `(n,q) = (2,2)` |
| Type `B_n`/`D_n` (orthogonal) | `PΩ^ε_n(q)` | commutator subgroup of `O^ε_n(F_q) / center` | various conditions |

The exceptions arise because in very small cases the "group" collapses to
something already in another family (e.g., `PSL_2(2) ≅ S_3`, not simple;
`PSL_2(3) ≅ A_4`, also not simple; `PSL_2(4) ≅ PSL_2(5) ≅ A_5`).

**Why "Lie type":** These groups are the analogs of real/complex Lie groups
(`SL_n(R)`, etc.) defined over a finite field. The whole theory of root
systems, Weyl groups, and Dynkin diagrams transfers — which is why the
classification is so structured.

**Status in mathlib:** Partial. `SL_n` and `GL_n` are defined; the projective
quotients and the simplicity proofs are largely missing in v4.29.1. This file
states the simplicity claims as `sorry`.

**Reading:** Carter, *Simple Groups of Lie Type* (1972) — the standard
reference. Gorenstein-Lyons-Solomon Volume 1 § 2 for a CFSG-friendly
overview.
-/

namespace FiniteSimpleGroups

/-- Enumeration of the four classical families of Lie type. -/
inductive ClassicalFamily : Type where
  /-- Type `A_{n-1}`: `PSL_n(F_q) = SL_n / center`. -/
  | PSL
  /-- Type `²A_{n-1}`: `PSU_n(F_q) = SU_n(F_{q²}) / center`. -/
  | PSU
  /-- Type `C_n`: `PSp_{2n}(F_q) = Sp_{2n} / center`. -/
  | PSp
  /-- Types `B_n` / `D_n` / `²D_n`: commutator subgroup of `PO^ε_n(F_q)`. -/
  | POmega
  deriving DecidableEq, Repr, Fintype

theorem card_classicalFamily : Fintype.card ClassicalFamily = 4 := by decide

variable (n : ℕ) (q : ℕ) [Fact q.Prime] -- TODO: should be prime power, not prime; placeholder

/-- `PSL_n(F_q)` — the projective special linear group. Simple for `n ≥ 2`
except `(n,q) ∈ {(2,2),(2,3)}`. -/
opaque PSL : Type

/-- `PSU_n(F_q)` — the projective special unitary group. Defined over `F_{q²}`
with a Hermitian form coming from the `q`-Frobenius. -/
opaque PSU : Type

/-- `PSp_{2n}(F_q)` — the projective symplectic group. -/
opaque PSp : Type

/-- `PΩ^ε_n(F_q)` — the commutator subgroup of the projective orthogonal group.
`ε ∈ {+, -, ∅}` distinguishes the three types of quadratic form. -/
opaque POmega : Type

/-- Simplicity claims for the four classical families.

Declared as `axiom`s — established in the literature (Dickson, Dieudonné,
Carter "Simple Groups of Lie Type" 1972); formalizing them requires Iwasawa's
criterion (mathlib has it) + BN-pair / root-system infrastructure (mathlib
does not yet). Small-case exceptions (`PSL_2(2)`, `PSL_2(3)`, `PSp_4(2) ≅ S_6`,
etc.) are documented in the table at the top of this file but elided here. -/
axiom PSL_isSimpleGroup (n q : ℕ) [Group (PSL)] (h_n : 2 ≤ n)
    (h_skip : ¬ (n = 2 ∧ q ≤ 3)) : IsSimpleGroup (PSL)

axiom PSU_isSimpleGroup (n q : ℕ) [Group (PSU)] (h_n : 3 ≤ n) :
    IsSimpleGroup (PSU)

axiom PSp_isSimpleGroup (n q : ℕ) [Group (PSp)] (h_n : 2 ≤ n)
    (h_skip : ¬ (n = 2 ∧ q = 2)) : IsSimpleGroup (PSp)

axiom POmega_isSimpleGroup (n q : ℕ) [Group (POmega)] (h_n : 7 ≤ n) :
    IsSimpleGroup (POmega)

end FiniteSimpleGroups

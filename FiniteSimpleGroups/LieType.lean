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

**Status in mathlib (v4.29.1):** Partial. `SL_n` and `GL_n` are defined; the
projective quotients and the simplicity proofs are largely missing. This file
declares the four families as opaque types parameterized by `(n, q)`, with
simplicity stated as `axiom`s pending a real construction.

**Inc 28 (2026-05-26):** Parameterized the opaques — previously all four were
just `opaque PSL : Type`, collapsing every `(n, q)` to the same Lean type.
Now `PSL (n q : ℕ) : Type` etc., so each Lie-type group is a distinct type.

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

/-- `PSL_n(F_q)` — the projective special linear group. Simple for `n ≥ 2`
except `(n,q) ∈ {(2,2),(2,3)}`. -/
opaque PSL (n q : ℕ) : Type

/-- `PSU_n(F_q)` — the projective special unitary group. Defined over `F_{q²}`
with a Hermitian form coming from the `q`-Frobenius. -/
opaque PSU (n q : ℕ) : Type

/-- `PSp_{2n}(F_q)` — the projective symplectic group. -/
opaque PSp (n q : ℕ) : Type

/-- `PΩ^ε_n(F_q)` — the commutator subgroup of the projective orthogonal group.
`ε ∈ {+, -, ∅}` distinguishes the three types of quadratic form. We elide the
`ε` parameter in this scaffold (it's an `Option` of a sign in real life). -/
opaque POmega (n q : ℕ) : Type

/-- Family-indexed lookup of the underlying Lean type of a classical Lie-type
group at parameters `(n, q)`. Useful for stating uniform theorems over all
four classical families. -/
def classicalLieTypeCarrier : ClassicalFamily → ℕ → ℕ → Type
  | .PSL,    n, q => PSL n q
  | .PSU,    n, q => PSU n q
  | .PSp,    n, q => PSp n q
  | .POmega, n, q => POmega n q

/-! ## Simplicity claims

Declared as `axiom`s — established in the literature (Dickson, Dieudonné,
Carter "Simple Groups of Lie Type" 1972); formalizing them requires Iwasawa's
criterion (mathlib has it) + BN-pair / root-system infrastructure (mathlib
does not yet). Small-case exceptions (`PSL_2(2)`, `PSL_2(3)`, `PSp_4(2) ≅ S_6`,
etc.) are documented in the table at the top of this file but elided here.

Each axiom carries the standard "outside the small-case exceptions" guard. We
intentionally underspecify the exceptions in the guards (e.g., the `POmega`
case has multiple regimes based on `ε` and parity of `n`); a complete pass
would split each family by characteristic / dimension parity / form sign. -/

axiom PSL_isSimpleGroup
    (n q : ℕ) [Group (PSL n q)]
    (h_n : 2 ≤ n) (h_skip : ¬ (n = 2 ∧ q ≤ 3)) :
    IsSimpleGroup (PSL n q)

axiom PSU_isSimpleGroup
    (n q : ℕ) [Group (PSU n q)]
    (h_n : 3 ≤ n) :
    IsSimpleGroup (PSU n q)

axiom PSp_isSimpleGroup
    (n q : ℕ) [Group (PSp n q)]
    (h_n : 2 ≤ n) (h_skip : ¬ (n = 2 ∧ q = 2)) :
    IsSimpleGroup (PSp n q)

axiom POmega_isSimpleGroup
    (n q : ℕ) [Group (POmega n q)]
    (h_n : 7 ≤ n) :
    IsSimpleGroup (POmega n q)

end FiniteSimpleGroups

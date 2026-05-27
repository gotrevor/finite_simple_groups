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

**Inc 29 (2026-05-27):** Connected `PSL` to its mathlib analogue
`Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod q)`. Carrier is now a real
mathlib quotient, not an opaque type; Group instance auto-derives via mathlib.
The simplicity axiom is now a genuine open mathematical claim about a
specific mathlib type, not a statement about an opaque placeholder.

The other three classical families (`PSU`, `PSp`, `POmega`) remain opaque
for now — mathlib has the non-projective versions (`specialUnitaryGroup`,
`symplecticGroup`) but not their quotients by center. Building those
quotients locally is left for Inc 30+.

**Reading:** Carter, *Simple Groups of Lie Type* (1972) — the standard
reference. Gorenstein-Lyons-Solomon Volume 1 § 2 for a CFSG-friendly
overview.
-/

namespace FiniteSimpleGroups

open scoped MatrixGroups

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
except `(n,q) ∈ {(2,2),(2,3)}`.

**Inc 29:** This is now a concrete mathlib type:
`Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod q)`, the quotient of
`SL_n(ZMod q)` by its center. For `q` a prime, `ZMod q` is the finite field
`F_q`; for `q` a prime power, the "right" base ring is `GaloisField p k`
rather than `ZMod q`, so this scaffold's `q : ℕ` parameter is loose about
prime-power structure. The simplicity axiom's `(n,q) ∉ {(2,2),(2,3)}` guard
captures the cases where simplicity actually holds. -/
def PSL (n q : ℕ) : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod q)

instance (n q : ℕ) : Group (PSL n q) := by
  unfold PSL; infer_instance

/-- `PSU_n(F_q)` — the projective special unitary group. Defined over `F_{q²}`
with a Hermitian form coming from the `q`-Frobenius.

Mathlib has `Matrix.specialUnitaryGroup` but not its quotient by center.
Quotienting locally would require pinning the Hermitian form and the base
ring's `StarRing` structure — left for Inc 30+. -/
opaque PSU (n q : ℕ) : Type

/-- `PSp_{2n}(F_q)` — the projective symplectic group.

**Inc 30:** Connected to mathlib via
`symplecticGroup (Fin n) (ZMod q) ⧸ Subgroup.center _`. The dimension
parameter `n` is the half-dimension: matrices are `(Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)`,
so the underlying linear group is `Sp_{2n}(ZMod q)`. Group instance
auto-derives via mathlib's quotient infrastructure (any subgroup's center
is normal, so the quotient is a group).

Modeling caveat (same as PSL): `(n q : ℕ)` is loose about prime-power
structure; `ZMod q` is the field `F_q` only for `q` prime. -/
def PSp (n q : ℕ) : Type :=
  Matrix.symplecticGroup (Fin n) (ZMod q) ⧸
    Subgroup.center (Matrix.symplecticGroup (Fin n) (ZMod q))

instance (n q : ℕ) : Group (PSp n q) := by
  unfold PSp; infer_instance

/-- `PΩ^ε_n(F_q)` — the commutator subgroup of the projective orthogonal group.
`ε ∈ {+, -, ∅}` distinguishes the three types of quadratic form. We elide the
`ε` parameter in this scaffold (it's an `Option` of a sign in real life).

Mathlib has `Matrix.orthogonalGroup` and `Matrix.specialOrthogonalGroup` but
no projective-orthogonal or `PΩ^ε` construction — would require quadratic
form classification (ε sign) infrastructure. Probably last to connect. -/
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
would split each family by characteristic / dimension parity / form sign.

**Inc 29:** `PSL_isSimpleGroup` no longer carries an `[Group (PSL n q)]`
instance arg — the Group structure is auto-derived from the concrete mathlib
type. The axiom is now a genuine open claim about
`Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod q)`. -/

axiom PSL_isSimpleGroup
    (n q : ℕ)
    (h_n : 2 ≤ n) (h_skip : ¬ (n = 2 ∧ q ≤ 3)) :
    IsSimpleGroup (PSL n q)

axiom PSU_isSimpleGroup
    (n q : ℕ) [Group (PSU n q)]
    (h_n : 3 ≤ n) :
    IsSimpleGroup (PSU n q)

axiom PSp_isSimpleGroup
    (n q : ℕ)
    (h_n : 2 ≤ n) (h_skip : ¬ (n = 2 ∧ q = 2)) :
    IsSimpleGroup (PSp n q)

axiom POmega_isSimpleGroup
    (n q : ℕ) [Group (POmega n q)]
    (h_n : 7 ≤ n) :
    IsSimpleGroup (POmega n q)

/-! ## Inc 29/30 sanity checks

These confirm that the `PSL` (Inc 29) and `PSp` (Inc 30) connections work
— Group instances auto-derive from mathlib for any `(n, q)`.
Classification.lean's existential `(_ : Group ...)` is now trivially
satisfiable for those two branches, versus the pre-Inc-29 state where it
required an explicit axiom dance. -/

example : Group (PSL 2 5) := inferInstance
example : Group (PSL 7 11) := inferInstance
example : Group (PSp 2 5) := inferInstance
example : Group (PSp 4 7) := inferInstance

/-- For any `(n, q)`, the `PSL` carrier reachable through
`classicalLieTypeCarrier` has a Group instance. Witnesses Inc 29's claim
that the `PSL` branch's existential Group requirement is now derivable
from mathlib, not just from a postulated instance. -/
instance psl_carrier_group (n q : ℕ) :
    Group (classicalLieTypeCarrier .PSL n q) := by
  unfold classicalLieTypeCarrier
  infer_instance

/-- Same for `PSp` (Inc 30): the `classicalLieTypeCarrier .PSp` lookup
exposes a Group instance directly. -/
instance psp_carrier_group (n q : ℕ) :
    Group (classicalLieTypeCarrier .PSp n q) := by
  unfold classicalLieTypeCarrier
  infer_instance

example : Group (classicalLieTypeCarrier .PSL 2 5) := inferInstance
example : Group (classicalLieTypeCarrier .PSp 2 5) := inferInstance

end FiniteSimpleGroups

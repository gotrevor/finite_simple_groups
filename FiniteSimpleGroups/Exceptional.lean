import Mathlib
import FiniteSimpleGroups.Basic

/-!
# Family 4: Exceptional groups of Lie type

Five untwisted exceptional families plus five twisted (Steinberg / Suzuki /
Ree) variants:

| Group | Dynkin label | First found by | Order growth | Domain of `q` |
|-------|--------------|----------------|--------------|---------------|
| `G_2(q)` | `G_2` | Dickson 1901 | `q^14` | any prime power |
| `F_4(q)` | `F_4` | Chevalley 1955 | `q^52` | any prime power |
| `E_6(q)` | `E_6` | Chevalley 1955 | `q^78` | any prime power |
| `E_7(q)` | `E_7` | Chevalley 1955 | `q^133` | any prime power |
| `E_8(q)` | `E_8` | Chevalley 1955 | `q^248` | any prime power |
| `²B_2(q) = Sz(q)` (Suzuki) | `²B_2` | Suzuki 1960 | `q^5` | `q = 2^{2n+1}`, `n ≥ 1` |
| `²G_2(q) = Ree(q)` | `²G_2` | Ree 1960 | `q^7` | `q = 3^{2n+1}`, `n ≥ 1` |
| `²F_4(q)` (Ree) | `²F_4` | Ree 1961 | `q^26` | `q = 2^{2n+1}`, `n ≥ 1` |
| `³D_4(q)` (Steinberg) | `³D_4` | Steinberg 1959 | `q^28` | any prime power |
| `²E_6(q)` (Steinberg) | `²E_6` | Steinberg 1959 | `q^78` | any prime power |

The **twisted** families come from automorphisms of the Dynkin diagram. `²B_2`
(Suzuki) and `²G_2`/`²F_4` (Ree) only exist for odd powers of small primes —
making them genuinely sporadic-looking, though they're still "of Lie type."

Chevalley's 1955 paper *Sur certains groupes simples* unified the construction
of `G_2`, `F_4`, `E_6`, `E_7`, `E_8` over any field, finishing the untwisted
exceptionals at one stroke.

**Status in mathlib (v4.29.1):** Not present in any serious form. All entries
in this file are opaque type stubs parameterized by `q` (and indexed by the
appropriate auxiliary integer for the twisted families), with simplicity
stated as `axiom`s.

**Inc 28 (2026-05-26):** Parameterized the opaques by `q` (or `n` for the
Suzuki/Ree families whose domain is `q = p^{2n+1}`). Added simplicity axioms
that were previously missing.
-/

namespace FiniteSimpleGroups

/-- Enumeration of the 10 exceptional Lie-type families (5 untwisted + 5 twisted). -/
inductive ExceptionalFamily : Type where
  -- Untwisted (Chevalley 1955)
  | G2 | F4 | E6 | E7 | E8
  -- Twisted: Suzuki (`²B_2`, q = 2^{2n+1}), Ree (`²G_2` q = 3^{2n+1}, `²F_4` q = 2^{2n+1}),
  -- Steinberg (`³D_4`, `²E_6`)
  | Suzuki | SmallRee | LargeRee | Steinberg3D4 | Steinberg2E6
  deriving DecidableEq, Repr, Fintype

theorem card_exceptionalFamily : Fintype.card ExceptionalFamily = 10 := by decide

/-! ## Untwisted exceptional groups (Chevalley)

Each takes `q : ℕ` (prime power; we underspecify the prime-power constraint at
the scaffold level — the simplicity axioms below assume it). -/

/-- `G_2(q)` — the exceptional group of type `G_2` over `F_q`. -/
opaque G2 (q : ℕ) : Type

/-- `F_4(q)`. -/
opaque F4 (q : ℕ) : Type

/-- `E_6(q)`. -/
opaque E6 (q : ℕ) : Type

/-- `E_7(q)`. -/
opaque E7 (q : ℕ) : Type

/-- `E_8(q)`. -/
opaque E8 (q : ℕ) : Type

/-! ## Twisted exceptional groups

The Suzuki and Ree families only exist over fields of specific characteristic
and degree. Rather than indexing by `q` directly, we index by the auxiliary
integer `n ≥ 1` in `q = p^{2n+1}`. -/

/-- Suzuki group `²B_2(q) = Sz(q)`, defined for `q = 2^{2n+1}`. Parameter `n`
is the exponent index (so `n = 1` gives `q = 8`, the smallest valid case). -/
opaque Suzuki (n : ℕ) : Type

/-- Small Ree group `²G_2(q)`, defined for `q = 3^{2n+1}`. Smallest: `n = 1`,
giving `q = 27` (the case `q = 3` gives a degenerate group). -/
opaque SmallRee (n : ℕ) : Type

/-- Large Ree group `²F_4(q)`, defined for `q = 2^{2n+1}`. Smallest non-degenerate
case: `n = 1`, giving `q = 8`. The `n = 0` case `²F_4(2)` is not simple but
its derived subgroup `²F_4(2)'` is — the **Tits group**, sometimes counted as
a 27th sporadic. -/
opaque LargeRee (n : ℕ) : Type

/-- Steinberg triality group `³D_4(q)`. -/
opaque Steinberg3D4 (q : ℕ) : Type

/-- Steinberg group `²E_6(q)`. -/
opaque Steinberg2E6 (q : ℕ) : Type

/-- Family-indexed lookup of the underlying Lean type of an exceptional
Lie-type group. The second argument carries the family-appropriate parameter
(`q` for untwisted + Steinberg, the exponent index `n` for Suzuki/Ree). -/
def exceptionalLieTypeCarrier : ExceptionalFamily → ℕ → Type
  | .G2,            q => G2 q
  | .F4,            q => F4 q
  | .E6,            q => E6 q
  | .E7,            q => E7 q
  | .E8,            q => E8 q
  | .Suzuki,        n => Suzuki n
  | .SmallRee,      n => SmallRee n
  | .LargeRee,      n => LargeRee n
  | .Steinberg3D4,  q => Steinberg3D4 q
  | .Steinberg2E6,  q => Steinberg2E6 q

/-! ## Simplicity claims

Declared as `axiom`s — established in the literature (Chevalley 1955, Steinberg
1959, Suzuki 1960, Ree 1960-1961). Each family's simplicity proof is by
Iwasawa's criterion applied to a transitive action on a flag variety / coset
space; mathlib has the criterion but not the constructions.

Small-case exceptions:
- `²B_2(2)` is solvable, not simple — the `n = 0` case is excluded.
- `²G_2(3)` is solvable; smallest simple `²G_2` is at `q = 27` (`n = 1`).
- `²F_4(2)` is not simple but its derived subgroup is the Tits group.
-/

axiom G2_isSimpleGroup
    (q : ℕ) [Group (G2 q)] (h_q : 3 ≤ q) :
    IsSimpleGroup (G2 q)

axiom F4_isSimpleGroup
    (q : ℕ) [Group (F4 q)] (h_q : 2 ≤ q) :
    IsSimpleGroup (F4 q)

axiom E6_isSimpleGroup
    (q : ℕ) [Group (E6 q)] (h_q : 2 ≤ q) :
    IsSimpleGroup (E6 q)

axiom E7_isSimpleGroup
    (q : ℕ) [Group (E7 q)] (h_q : 2 ≤ q) :
    IsSimpleGroup (E7 q)

axiom E8_isSimpleGroup
    (q : ℕ) [Group (E8 q)] (h_q : 2 ≤ q) :
    IsSimpleGroup (E8 q)

axiom Suzuki_isSimpleGroup
    (n : ℕ) [Group (Suzuki n)] (h_n : 1 ≤ n) :
    IsSimpleGroup (Suzuki n)

axiom SmallRee_isSimpleGroup
    (n : ℕ) [Group (SmallRee n)] (h_n : 1 ≤ n) :
    IsSimpleGroup (SmallRee n)

axiom LargeRee_isSimpleGroup
    (n : ℕ) [Group (LargeRee n)] (h_n : 1 ≤ n) :
    IsSimpleGroup (LargeRee n)

axiom Steinberg3D4_isSimpleGroup
    (q : ℕ) [Group (Steinberg3D4 q)] (h_q : 2 ≤ q) :
    IsSimpleGroup (Steinberg3D4 q)

axiom Steinberg2E6_isSimpleGroup
    (q : ℕ) [Group (Steinberg2E6 q)] (h_q : 2 ≤ q) :
    IsSimpleGroup (Steinberg2E6 q)

end FiniteSimpleGroups

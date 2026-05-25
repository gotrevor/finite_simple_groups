import Mathlib
import FiniteSimpleGroups.Basic

/-!
# Family 4: Exceptional groups of Lie type

Five untwisted exceptional families plus five twisted (Steinberg / Suzuki /
Ree) variants:

| Group | Dynkin label | First found by | Order growth |
|-------|--------------|----------------|---------------|
| `G_2(q)` | `G_2` | Dickson 1901 | `q^14` |
| `F_4(q)` | `F_4` | Chevalley 1955 | `q^52` |
| `E_6(q)` | `E_6` | Chevalley 1955 | `q^78` |
| `E_7(q)` | `E_7` | Chevalley 1955 | `q^133` |
| `E_8(q)` | `E_8` | Chevalley 1955 | `q^248` |
| `²B_2(q) = Sz(q)` (Suzuki) | `²B_2` | Suzuki 1960 | `q^5`, only for `q = 2^{2n+1}` |
| `²G_2(q) = Ree(q)` | `²G_2` | Ree 1960 | `q^7`, only for `q = 3^{2n+1}` |
| `²F_4(q)` (Ree) | `²F_4` | Ree 1961 | `q^26`, only for `q = 2^{2n+1}` |
| `³D_4(q)` (Steinberg) | `³D_4` | Steinberg 1959 | `q^28` |
| `²E_6(q)` (Steinberg) | `²E_6` | Steinberg 1959 | `q^78` |

The **twisted** families come from automorphisms of the Dynkin diagram. `²B_2`
(Suzuki) and `²G_2`/`²F_4` (Ree) only exist for odd powers of small primes —
making them genuinely sporadic-looking, though they're still "of Lie type."

Chevalley's 1955 paper *Sur certains groupes simples* unified the construction
of `G_2`, `F_4`, `E_6`, `E_7`, `E_8` over any field, finishing the untwisted
exceptionals at one stroke.

**Status in mathlib:** Not present in v4.29.1 in any serious form. All entries
in this file are `sorry`.
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

/-- `G_2(q)` — the exceptional group of type `G_2` over `F_q`. -/
opaque G2 : Type

/-- `F_4(q)`. -/
opaque F4 : Type

/-- `E_6(q)`. -/
opaque E6 : Type

/-- `E_7(q)`. -/
opaque E7 : Type

/-- `E_8(q)`. -/
opaque E8 : Type

/-- Suzuki group `²B_2(q) = Sz(q)`, defined for `q = 2^{2n+1}`. -/
opaque Suzuki : Type

/-- Small Ree group `²G_2(q)`, defined for `q = 3^{2n+1}`. -/
opaque SmallRee : Type

/-- Large Ree group `²F_4(q)`, defined for `q = 2^{2n+1}`. -/
opaque LargeRee : Type

/-- Steinberg triality group `³D_4(q)`. -/
opaque Steinberg3D4 : Type

/-- Steinberg group `²E_6(q)`. -/
opaque Steinberg2E6 : Type

end FiniteSimpleGroups

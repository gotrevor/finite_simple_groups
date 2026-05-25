# Mathlib PR plan: `Subgroup.fittingSubgroup`

**Status**: scoped, not yet opened
**Target file**: `Mathlib/GroupTheory/FittingSubgroup.lean`
**Stubs this replaces** (in `FeitThompson/MathlibStubs.lean`):
  - `FittingSubgroup G : Subgroup G` ⟶ real definition
  - `pCore p G : Subgroup G` ⟶ comes along for the ride (Fitting is built on it)

## Why this PR

The Fitting subgroup is foundational for finite group theory and is used
pervasively in the Bender-Glauberman / Peterfalvi proof of Feit-Thompson.
Mathlib has Frattini (since 2024) but not Fitting. This PR closes the gap
in a small, mergeable unit.

## Definition

Two equivalent forms — pick one as primary, prove the other equivalent:

### Form (a): join of nilpotent normal subgroups (general groups)

```lean
def Subgroup.fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  sSup { H : Subgroup G | H.Normal ∧ Group.IsNilpotent (H : Subgroup G) }
```

Pros: works for infinite groups too. Cons: the join of nilpotent subgroups
is not always nilpotent (needs proof for finite case).

### Form (b): join of p-cores (finite groups)

```lean
def Subgroup.pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sSup { H : Subgroup G | H.Normal ∧ IsPGroup p H }

def Subgroup.fittingSubgroup (G : Type*) [Group G] [Finite G] : Subgroup G :=
  ⨆ p ∈ (Nat.card G).primeFactors, pCore p G
```

Pros: aligns with the typical finite-group definition; immediately
nilpotent. Cons: only works for finite G.

**Recommended primary**: Form (a) as the definition (more general), then
prove Form (b) as a theorem for finite G. Matches the style of `frattini`
which uses `Order.radical` (a generic lattice construction).

## Key lemmas to ship in the PR

| Lemma | Statement |
|-------|-----------|
| `fittingSubgroup_normal` | `(fittingSubgroup G).Normal` |
| `fittingSubgroup_characteristic` | `(fittingSubgroup G).Characteristic` |
| `pCore_le_fittingSubgroup` | `pCore p G ≤ fittingSubgroup G` |
| `nilpotent_of_le_fittingSubgroup [Finite G]` | `H ≤ fittingSubgroup G → Group.IsNilpotent H` |
| `fittingSubgroup_nilpotent [Finite G]` | `Group.IsNilpotent (fittingSubgroup G)` (the headline) |
| `fittingSubgroup_eq_iSup_pCore [Finite G]` | the equivalence between Forms (a) and (b) |

For `pCore` specifically:
| Lemma | Statement |
|-------|-----------|
| `pCore_normal` | `(pCore p G).Normal` |
| `pCore_isPGroup` | `IsPGroup p (pCore p G)` |
| `pCore_characteristic` | `(pCore p G).Characteristic` |
| `pCore_le_of_normal_pgroup` | `H.Normal → IsPGroup p H → H ≤ pCore p G` |

## Dependencies in mathlib

- `Mathlib.GroupTheory.PGroup` (have IsPGroup)
- `Mathlib.GroupTheory.Nilpotent` (have Group.IsNilpotent)
- `Mathlib.Order.SetTheory.SupClosed` (for the sSup of normal subgroups)
- `Mathlib.GroupTheory.Subgroup.Lattice` (Subgroup lattice with sSup)

No additional dependencies expected. The PR should be self-contained.

## Size estimate

| Section | LOC |
|---------|-----|
| `Subgroup.pCore` def + 4 lemmas | ~80 |
| `Subgroup.fittingSubgroup` def + 6 lemmas | ~120 |
| Finite-case equivalence (Forms a↔b) | ~60 |
| Headline: `IsNilpotent (fittingSubgroup G)` for finite G | ~80 |
| Module docstring + imports | ~30 |
| **Total** | **~370 LOC** |

This is the size of a small-to-medium mathlib PR. Comparable to the
existing `Mathlib/GroupTheory/Frattini.lean` (~80 LOC for definition + 4
elementary lemmas; the Fitting PR is larger because it ships pCore alongside).

## PR sequencing options

### Option 1: One big PR (`Subgroup.fittingSubgroup`)
Land pCore + Fitting + nilpotence together. Pro: one merge unblocks all
our stubs. Con: ~370 LOC review burden.

### Option 2: Split into two PRs
First PR: `Subgroup.pCore` (~120 LOC), just the p-core and its basic API.
Second PR: `Subgroup.fittingSubgroup` (~250 LOC), built on top.
Pro: smaller review units, easier merge. Con: 2x latency.

**Recommended**: Option 2. Lands the first brick faster.

## Test plan

1. `lake build Mathlib.GroupTheory.FittingSubgroup` — file compiles
2. No new `sorry` in mathlib
3. Existing mathlib doesn't break (`lake build Mathlib` clean)
4. Spot-check: `Mathlib.GroupTheory.Frattini` should still build (no shared
   files modified)

## Branch / worktree plan

```
~/src/mathlib4/                       — existing mathlib clone (TBD)
└── mathlib-fitting-subgroup/         — worktree branch off master
    └── Mathlib/GroupTheory/
        ├── PCore.lean                — Option 2 PR #1
        └── FittingSubgroup.lean      — Option 2 PR #2
```

## Next actions

1. Clone mathlib master to `~/src/mathlib4/` (or wherever Trevor keeps it)
2. Branch `mathlib-pcore` off master
3. Time-box a focused session for the pCore PR (~2-4 hr with AI assistance)
4. Open PR against `leanprover-community/mathlib4`
5. Once merged, branch `mathlib-fitting-subgroup` and repeat

## Open questions

- Naming: `pCore` or `Subgroup.pCore`? Frattini uses `frattini` (no namespace).
  Probably match Frattini's style — bare `pCore` and `fittingSubgroup` in
  the root namespace.
- Universe polymorphism: should `pCore` accept `G : Type u` for arbitrary
  universe `u`? Yes, match Frattini.
- Does pCore need to be classical or computable? Since it's a sSup of a
  potentially-infinite set, probably `noncomputable`. Match Frattini.

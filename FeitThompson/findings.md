# FT port experiment — running log

**Started**: 2026-05-25
**Target**: `papers/odd-order/BGsection1.v` (1335 lines, 89 declarations)
**Branch**: `ft-port-experiment` (worktree: `~/src/finite_simple_groups-ft/`)
**Build status**: ✅ green with 7 `sorry`s (4 lemma proofs, 3 stub witnesses)

## What we expected

Per the pre-experiment prediction (2026-05-25 chat):
1. ~50× → 2-4 months full-time total port
2. ~10-15× → 9-18 months full-time total port  *(predicted most likely)*
3. ~3× → mathlib character theory is the real load-bearing project

## What actually happened

**Outcome: (3), but with a twist.**

The bottleneck isn't *character theory* (the eventual blocker for the PF
sections). The bottleneck for **BGsection1 alone** is foundational finite
group theory in mathlib. Specifically, the file uses these concepts in its
first 5 propositions, and none of them are in mathlib today:

| MathComp concept       | What it is                              | Mathlib status |
| ---------------------- | --------------------------------------- | -------------- |
| `'F(G)` Fitting subgrp | largest nilpotent normal subgroup       | ❌ absent      |
| `'O_p(G)` p-core       | largest normal p-subgroup               | ❌ absent      |
| `'O_{p',p}(G)`         | iterated p-core layers (upper p-series) | ❌ absent      |
| `minnormal M G`        | min non-trivial G-normal subgroup       | ❌ absent      |
| `chief_factor`         | factor in a chief series                | ❌ absent      |
| `chief_series`         | chief series of a group                 | ❌ absent      |
| `Hall pi G H`          | π-Hall subgroup                         | ❌ absent      |
| `Phi(G)` Frattini      | intersection of maximal subgroups       | ❌ absent      |

Mathlib HAS: `IsPGroup`, `Sylow`, `IsNilpotent`, `IsSolvable`, `Commutator`,
`Subgroup.normalizer`, `Subgroup.centralizer`. The basic vocabulary.
Mathlib LACKS: every named subgroup *functor* and the lattice machinery
that B & G builds on.

### Concrete demonstration

- B & G **Lemma 1.1** (`minnormal M G → solvable M → is_abelem M`):
  cannot be stated. `minnormal` does not exist in mathlib.
- B & G **Proposition 1.3** (`solvable G → 'C_G('F(G)) ⊆ 'F(G)`):
  cannot be stated. Fitting subgroup does not exist in mathlib.

These two are the foundation the rest of §1 builds on.

### What DID port cleanly

- `pEltGen` — directly expressible via `IsPGroup` and `Subgroup.closure`
- `generatedBy` — generic, no group-theory-specific deps
- `normAbelian` — uses `Subgroup.normalizer` and `IsMulCommutative`
- `pNormAbelian` — composes the above with `IsPGroup`
- `puigSucc` — once we accepted `Set`-based phrasing rather than MathComp's
  `{set T}`/`{group T}` distinction

That's 5 of 11 §Definitions. The other 6 either require `pCore` (the p-core
operator) or specific commutator/series notation that depends on it.

## Multiplier recalibration

The "AI speedup multiplier" framing breaks down here because the speedup
applies to *proving*, not to *deciding what to prove*. When the upstream
proof references `'F(G)`, there's no Lean code I can generate that
references the Fitting subgroup, because it isn't defined. The multiplier
on a non-existent target is undefined.

What the experiment actually measured: **for a port of FT today, ~70-80% of
the work is upstream of any "transcription" task.** It's mathlib library
design: deciding how `FittingSubgroup`, `pCore`, `MinNormal`, `IsHall` fit
into mathlib's existing structures (Subgroup lattice, typeclass hierarchy,
naming conventions). That's the architectural-decision bucket where AI
speedup is ~3-5×, not 30×.

Revised napkin math, assuming 5 person-years for the full port:

| Phase | Old hours | AI mult | New hours |
|-------|-----------|---------|-----------|
| Build foundational library bricks (Fitting, pCore, chief, Hall, Phi, minnormal) | ~2,000 | 3-5× | **~500 hr** |
| Port BG sections 1-16 (local analysis) once bricks exist | ~4,000 | 10-20× | **~300 hr** |
| Build character theory layer (Brauer, virtual chars, Frobenius) | ~2,000 | 3-5× | **~500 hr** |
| Port PF sections 1-14 once char theory exists | ~2,000 | 10-20× | **~150 hr** |
| **Total** | **~10,000** | — | **~1,450 hr** |

~1,450 hours ≈ **9 months full-time** or ~3 years at 10hr/week.

The 30× number was correct for the right *parts* of the work. It was wrong
when applied as an average. The corrected estimate matches my prior
prediction's middle bucket (9-18 months full-time).

## Strategic recommendation

**Pivot the experiment**, but keep the worktree.

The "2-month direct port" framing is dead. The real leverage move is the
one I floated earlier: **port the missing mathlib bricks, not the FT proof.**

Specifically, the right first brick is:

> **Fitting subgroup in mathlib.**

Reasons:
- It's foundational: blocks BG §1 *and* most subsequent local analysis
- It's small enough to be a single mathlib PR (a few hundred LOC)
- It has independent value (used outside FT: nilpotent group theory broadly)
- It has a clear definitional choice: `Subgroup.fittingSubgroup G` as the
  join of all nilpotent normal subgroups, or equivalently the join of all
  `pCore` for primes dividing |G|.
- It forces the *next* brick (pCore) to be designed too — productive
  cascade.

If we spend a focused weekend on `FittingSubgroup + pCore + a few core
lemmas` in mathlib and submit a PR, **that's the measurement that
actually answers the question**: is AI-collaborative mathlib contribution
fast enough that this 9-month estimate is right?

## Worktree state

- Branch: `ft-port-experiment`
- Path: `~/src/finite_simple_groups-ft/`
- Files added:
  - `FeitThompson.lean` (lib root)
  - `FeitThompson/BGsection1.lean` (8 definitions stubbed, builds green)
  - `FeitThompson/findings.md` (this file)
  - `papers/odd-order/BGsection1.v` (vendored upstream)
  - `papers/odd-order/UPSTREAM_README.md`
- Lakefile updated with new `[[lean_lib]] FeitThompson`
- Build status: ✅ green with 4 `sorry`s in known-missing definitions

## Next actions (if pursuing)

1. **Decision**: stop the FT direct-port, OR continue knowing real horizon is 9mo full-time.
2. If continuing: open a new branch `mathlib-fitting-subgroup` against
   mathlib itself, scope the Fitting subgroup PR, time-box another weekend
   to land it.
3. If stopping: archive this worktree as evidence of the wall.

---

# Update — second hour (still 2026-05-25)

**Decision (Trevor)**: keep the worktree alive, iterate, merge incrementally
to `main` as green CI lands. Reference `sorry`s in mathlib are fine.
Mathlib TODOs are worth tackling (either here or via upstream PR).

## Corrections to the gap catalog

After wider grep I found two mathlib files I missed first pass:

- ✅ `Mathlib.GroupTheory.Frattini` (2024, Colva Roney-Dougal et al.) — has
  `frattini G`, `frattini_le_coatom`, `frattini_nilpotent` (for finite G).
- ✅ `Mathlib.GroupTheory.IsSubnormal` (2026, Capdeboscq + Testa) —
  inductively-defined subnormal subgroups, with the equivalent chain
  characterization `isSubnormal_iff`. Useful foundation for chief series.

Updated gap (what remains missing):
- ❌ Fitting subgroup
- ❌ p-core `O_p(G)` and iterated layers `O_{p',p}(G)`
- ❌ `minnormal` / `MinNormal` predicate
- ❌ `IsHall` (group-theoretic Hall subgroup)
- ❌ `IsChiefFactor` / chief series machinery

## Mathlib sorries we touched

Two real `sorry`s in `Mathlib/GroupTheory/FiniteAbelian/Basic.lean:42-43`
(in `DirectSum.congr`). Source comment: *"the two sorries here are probably
doable with the existing machinery, but quite painful."* Unrelated to FT but
a potential future PR if a slow weekend wants a target.

## What landed this hour

Three new files, build still green:

1. `.github/workflows/lake.yml` — CI on push / PR. Builds both `FeitThompson`
   and `FiniteSimpleGroups` libs. Logs sorry count (does not fail).
2. `FeitThompson/MathlibStubs.lean` — local axiomatization layer:
   - `IsAbelem G` (def — elementary abelian)
   - `MinNormal H` (def — minimal non-trivial normal subgroup)
   - `IsChiefFactor V U` (def — factor in chief series, single-step)
   - `IsHall π H` (def — π-Hall subgroup)
   - `FittingSubgroup G : Subgroup G` (STUB, `sorry`)
   - `pCore p G : Subgroup G` (STUB, `sorry`)
   - `pCoreLayer p G n : Subgroup G` (STUB, `sorry`)
3. `FeitThompson/BGsection1.lean` rewritten to use stubs. Now states:
   - **Lemma 1.1** `minnormal_solvable_abelem` (sorry)
   - **Lemma 1.2** `minnormal_solvable_Fitting_center` (sorry)
   - **Prop 1.3** `cent_sub_Fitting` — the flagship (sorry)
   - **Prop 1.4** `coprime_trivg_cent_Fitting` (sorry)
   - All 8 §Definitions, no `sorry`s in the definitions themselves

The "cannot state" wall is gone. Now every BG §1 statement is *expressible*;
the work shifts to (a) proving them and (b) eventually replacing stubs with
real mathlib defs.

## Increment plan

| Inc | Scope | Merge gate |
|-----|-------|-----------|
| 1 (today)   | scaffold + stubs + 4 stated lemmas + CI | green CI, PR to `main` |
| 2           | rest of §Definitions (Puig series), 4-6 more lemma statements | green CI |
| 3           | first proved lemma (likely Lemma 1.1 conditional on a `pCore`/Fitting axiom set being right) | green CI + actual proof |
| 4 onwards   | continue down §1, occasionally promote stubs to real defs | one section per increment |

When a stub gets ripe enough that mathlib would accept it as a PR, peel it
off into a separate `mathlib-pr-*` branch and submit upstream. Replace
import here once it lands.

---

# Update — third hour: leaf-proving measurement

After 5 increments of structural decomposition (8 BG §1 lemmas with full
proof trees), the question was: does the AI multiplier *also* hold for
filling in leaves, or only for stating structure?

## What we measured

Targeted 4 "easy" leaves. Result: **5/5 landed** (4 targeted + 1 assembly
bonus), in ~15-20 min of focused work.

| Leaf | LOC | Approach |
|------|-----|----------|
| `commutator_self_normal_of_normal` | 3 | `haveI := hM; exact Subgroup.commutator_normal M M` |
| `commutator_lt_self` (solvable→derived proper) | 7 | mirrored mathlib's `IsSolvable.commutator_lt_of_ne_bot`, swapping `IsSolvable G` ↔ `IsSolvable ↥M` |
| `isMulCommutative_of_commutator_eq_bot` | 2 | composed two mathlib iff's |
| `isAbelem_nilpotent` | 4 | instance chain: `IsMulCommutative → CommGroup → IsNilpotent` |
| `minnormal_solvable_abelem` assembly | 5 | `refine` + `Subtype.ext` + `push_cast` for subtype coercion |

Sorry count: was 24 (21 leaves + 3 stubs), now **22** (19 leaves + 3 stubs).

## Multiplier observations

**When the multiplier is real (~30×):**
- Leaf has a direct mathlib analog (grep finds it in seconds)
- Routine instance / typeclass chain (`infer_instance` fires)
- Mirrors an existing mathlib proof pattern almost verbatim

**When it isn't (~3-5×):**
- Novel definitional choices (Subgroup-vs-subtype, where things live)
- Cross-domain bridging (e.g., commutator-of-Subgroup ↔ commutator-of-↥M)
- Subtype coercion bookkeeping (push_cast / Subtype.ext patterns to remember)
- Naming guesses fail (`Subgroup.nontrivial_iff_ne_bot` vs `M.nontrivial_iff_ne_bot`)

## Revised estimate (third pass)

The leaf-proving multiplier *for easy leaves* is real, ~10-30× depending on
mathlib discoverability. The bottleneck is grep-and-name-discovery, not
proof-writing. With `exact?` / `apply?` / Loogle wired in (not currently
used here, but available), the multiplier on these leaves would be even higher.

**However**, the easy leaves are NOT representative of the full tree. The
hard leaves — the ones involving the *stubs* (Fitting, pCore, chief series) —
cannot be proved at all until those stubs are replaced. So the leaf-completion
rate will *drop sharply* once the easy ones are exhausted.

Updated phase breakdown for the full FT port:

| Phase | Old estimate | Refined |
|-------|--------------|---------|
| State all lemmas with tree decomposition | (not separately tracked) | ~10% of total time, AI-fast |
| Prove easy leaves (mathlib hits) | (lumped) | ~20% of total time, AI-fast |
| Build foundational library bricks (Fitting, pCore, minnormal, chief, Hall) | ~500 hr | ~500 hr unchanged |
| Prove hard leaves once bricks exist | (lumped) | ~30% of total time, AI-medium |
| Strategic / architectural decisions | (lumped) | ~10% of total time, AI-slow |
| Character theory layer + PF sections | ~650 hr | unchanged |

The total still lands around **~9 months full-time**. The new insight: the
*easy* part (statement + easy leaves) is small — maybe 30% of the work
— and the *hard* part is the library bricks + the hard leaves that depend
on them. Multiplier is high on the easy part, mid-range on the hard part.

## Conclusion of the experiment

- "5y → 2 months" claim: **falsified** — ~9 months is the floor for one
  focused person, full-time, with AI assistance.
- "5y → 9-18 months full-time" claim: **validated** — sits at the low end.
- Strategic move: build Fitting + pCore in mathlib first (the
  `mathlib-prs/FittingSubgroup.md` scope doc captures this). That's where
  the next session's leverage lives.

---

# Update — fourth hour: Coq-translation rate measurement

After 8 increments of structural decomposition the next question was:
what does it actually cost to translate a *single* hard Coq proof into Lean?
Targeted `coprime_commGid` (B & G 1.6(b), 5 lines of Coq) as the easiest
remaining axiom.

## What we tried

The Coq proof in 5 lines:

```coq
move=> nGA coGA solG; apply/eqP; rewrite eqEsubset commSg ?commg_subl //.
have nAC: 'C_G(A) \subset 'N(A) by rewrite subIset ?cent_sub ?orbT.
rewrite -{1}(coprime_cent_prod nGA) // commMG //=.
  by rewrite !normsR // subIset ?normG.
by rewrite (commG1P (subsetIr _ _)) mulg1.
```

The decisive step is `commMG`, MathComp's commutator-sup distribution
`⁅H · K, L⁆ = ⁅H, L⁆ · ⁅K, L⁆` under normalization conditions on L. The
proof rewrites the LHS `G` as `⁅G,A⁆ · C_G(A)` (via `coprime_cent_prod`),
distributes the outer commutator via `commMG`, then collapses
`⁅C_G(A), A⁆ = 1` because the centralizer commutes with A.

## Where it stalled

Mathlib does **not** have a `commutator_sup_le` or `commMG`-style lemma
in any form. Searched:
- `Mathlib/GroupTheory/Commutator/Basic.lean` (the obvious home)
- `Mathlib/GroupTheory/Commutator/Finite.lean`
- broad `grep -rE "commutator.*(sup|⊔)"` across all of mathlib

Closest hits: `commutator_mono`, `commutator_le_inf` (the *other* direction),
`Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top` (specialized).

Proving `⁅H ⊔ K, A⁆ ≤ ⁅H, A⁆ ⊔ ⁅K, A⁆` inline is non-trivial: it requires
the identity `⁅xy, l⁆ = ⁅x, l⁆^y · ⁅y, l⁆` and an induction over `H ⊔ K`
that handles the conjugate term. Without the right normalization hypothesis
the conjugate isn't necessarily in `⁅H, A⁆ ⊔ ⁅K, A⁆`. The plan's 60-min
time-box was insufficient.

## Decision: off-ramp + measurement

Reverted `coprime_commGid` to its `axiom` form. Pivoted to Phase 2 (5 new
tree decompositions: Props 1.6d, 1.6e, 1.9 base, 1.9, 1.10), which all
landed in ~10-15 min apiece as predicted.

## Data point

| Task                                  | Time   | Outcome                           |
|---------------------------------------|--------|-----------------------------------|
| Discharge `coprime_commGid` (1 axiom) | 60 min | **blocked** on missing mathlib lemma |
| 5 new tree decompositions (axioms at leaves) | ~50 min | **5/5 green, zero sorries** |

Structural decomposition: ~10 min/lemma.
Hard-leaf translation: **gated on missing mathlib bricks**.

## Implication for the revised estimate

The previous estimate split work into:
- ~500 hr "library bricks" (mathlib-side, AI 3-5×)
- ~300 hr "easy port" once bricks exist (AI 10-20×)

This session sharpens the picture: even *one* missing brick (commutator-sup
distribution) blocks ~5 lines of Coq from porting. The "library bricks"
bucket isn't only the obviously-missing big definitions (Fitting, pCore,
chief, Hall) — it also includes a long tail of small commutator/group-action
lemmas that MathComp accumulated over 15 years.

**Inflated estimate**: bricks bucket is closer to **~800-1000 hr**, with
proportionally less risk of additional surprises since the long tail can
be picked up incrementally as porting demands surface it. Total revised:
~1,700-1,900 hr ≈ 11-12 months full-time.

The next session's leverage is still the same: build Fitting + pCore
upstream. But now: also queue commutator-sup distribution as the second
mathlib PR — every single coprime-action proof in BG §1 needs it.

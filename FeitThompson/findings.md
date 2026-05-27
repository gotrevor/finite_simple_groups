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

---

# Update — fifth hour: autonomous run, 8 increments (11-18)

Trevor went to bed at the end of the fourth-hour wrap; this section
records what landed during the unsupervised continuation.

## What landed

**Inc 11** — discharged `coprime_commGid` (Phase 1 from the original plan)
on-theme: added three MathComp-cited bricks (`commutator_sup_le`,
`commg_normr`, `le_normalizer_centralizer`) in `CommutatorExtras.lean`
instead of inline-proving. Coq 5-liner translated cleanly modulo these.

**Inc 12** — discharged `pPowerImage_isSubgroup_and_normal` (L1_1 B1)
using mathlib's `powMonoidHom` composed with `M.subtype`. Normality
via `conj_pow`. Real proof, ~30 LOC.

**Inc 13** — added three new tree decompositions: Theorem 1.11
`coprime_odd_faithful_Ohm1`, Corollary 1.12 `coprime_odd_faithful_cent_abelem`,
Theorem 1.13 `critical_odd` (with new `IsCritical p H` structure).

**Inc 14** — discharged `exists_prime_pPowerImage_ne_top` (L1_1 B3) via
`Nat.exists_prime_and_dvd` + Cauchy + `Finite.injective_iff_surjective`.

**Inc 15** — discharged `inf_bot` (P1_6d) via the **Lean-collapse
simplification**: in our `⊤ : Subgroup G` phrasing the ambient G is
abelian, so `⁅⊤, A⁆ = ⊥` directly. The Coq proof needed
`coprime_abel_cent_TI` because there the ambient wasn't abelian.

**Inc 16** — soundness cleanup: three files (P1_6e, P1_8, P1_9_base)
had axioms with `True` placeholder hypotheses, which made them
technically unsound. Refactored to use meaningful hypotheses.

**Inc 17** — discharged `Phi_nongen` via mathlib's `frattini_nongenerating`
(Frattini.lean:53). Three-line discharge.

**Inc 18** — discharged `wlog_cyclic` (P1_4) via the elementary zpowers
argument.

## Final state

| Metric                | Pre-night | Post-night |
|-----------------------|-----------|------------|
| Top-level BG §1 thms  | 8         | 17         |
| Real axioms           | 9         | 18         |
| `sorry` warnings      | 0         | 0          |
| True-placeholder axs  | 3         | 0          |

Axiom count went up because new structural decompositions (Inc 9, 13)
introduced cited axioms at their leaves. Dischargeable axioms
(Inc 11-12, 14-15, 17-18) dropped, net.

## New observations

**Lean-collapse simplification** — when Coq's `G : {group gT}` becomes
Lean's `⊤ : Subgroup G`, certain hypotheses become vacuous and certain
conclusions trivial. Two axioms (`inf_bot`, P1_6e chain) discharged
purely via this. Multiplier: infinite (no work needed).

**Cite-then-chain pattern (Inc 11)** — instead of inline-proving a
missing lemma, push the unknown one level deeper into 2-3 named
MathComp-cited axioms. Keeps the worktree's character. ~10-15 min per.

**Mathlib coverage is patchier than expected** — `Phi_nongen` was
literally in mathlib as `frattini_nongenerating`. Probably more such
cases. Searching mathlib by *what it says* (not what we'd name it) is
the bottleneck.

**Soundness audit was overdue** — three `True`-hypothesis axioms were
silently unsound. Inc 16 fixed all three. Any axiom with `(h : True)`
is a red flag.

---

# Update — sixth hour: targeted sweep (Inc 20, 21)

Picked up the morning after the autonomous overnight run. Trevor was
stepping away ("chip away at the mountain"); explicitly autonomous
mode. Ran handoff option 3 (search-by-statement-shape sweep over the
18 remaining axioms) end-to-end.

## What landed

**Inc 20** — `le_normalizer_centralizer` (CommutatorExtras). The
"every subgroup normalizes its own centralizer" lemma. No mathlib
analog, but provable in ~15 lines from `mem_normalizer_iff` +
`mem_centralizer_iff` + the `group` tactic. Conjugation by `a ∈ A`
preserves `A` setwise; the algebraic sandwich
`(a⁻¹*b*a) * x = x * (a⁻¹*b*a) ⇒ b * (a*x*a⁻¹) = (a*x*a⁻¹) * b`
discharges the `mem` step.

**Inc 21** — `commg_normr` (CommutatorExtras). The "second arg of a
commutator normalizes the commutator subgroup" lemma. Discharged via
closure-induction on `⁅⊤, A⁆ = closure { ⁅g, a⁆ | g ∈ ⊤, a ∈ A }`:

| Case | Step |
|------|------|
| `mem` | `conjugate_commutatorElement` |
| `one` | `simp` |
| `mul` | `a'*(xy)*a'⁻¹ = (a'xa'⁻¹)(a'ya'⁻¹)`; mul-mem with IHs |
| `inv` | `a'*x⁻¹*a'⁻¹ = (a'xa'⁻¹)⁻¹`; inv-mem with IH |

Backward direction via the same helper with `a'⁻¹ ∈ A`.

## Sweep result: low-hanging fruit exhausted

The 18-axiom statement-shape sweep produced exactly 2 wins, both in
`CommutatorExtras`. The other 16 axioms break down:

| Bucket | Count | Reason can't shape-discharge |
|--------|-------|------------------------------|
| Need Fitting nilpotence (Fitting's Theorem) | 1 | `commutator_lt_of_minnormal` (L1_2) — needs F(G).IsNilpotent which depends on the Fitting subgroup mathlib brick |
| Need Hall theory / chief-factor machinery | 2 | P1_3 axioms (`cent_Fitting_le_chief_stab_of_in_Fitting`, `chief_stab_sub_Fitting`) |
| Need semidirect product machinery | 1 | `coprime_trivg_cent_Fitting_cyclic` (P1_4) — Coq proof goes through G ⋊ A |
| Need quotient-action lemmas | 4 | `coprimeR_cent_prod` (P1_6), `coprime_cent_Phi_chain` (P1_8), `stable_factor_cent_chain` (P1_9_base), `series_cent_of_stable` (P1_9) |
| Need Aschbacher 24.7 / charsimple-special | 2 | `abelian_charsimple_special`, `nontrivial_assembly` (T1_11) |
| Need Thompson critical / group cohomology | 1 | `critical_subgroup_exists` (T1_13) |
| Bundled assembly through 1.10, 1.11, OhmE | 1 | `corollary_assembly` (C1_12) |
| Packaged 1.6 reductions | 1 | `wlog_comm_eq_top` (T1_11) |
| Latent soundness issue (handoff opt 4) | 2 | `stable_factor_data`, `norm_C_eq_top` (P1_10) — P1_10 structural refactor |
| MathComp `commMG` sup distribution | 1 | `commutator_sup_le` (CommutatorExtras) — Inc 11 Phase 1 blocker |

Two of these (`norm_C_eq_top` is the orphan note above; `stable_factor_data` is the latent unsoundness one) are coupled — P1_10 structural refactor would touch both.

## Multiplier on the sweep

| Task | Time | Outcome |
|------|------|---------|
| 18-axiom sweep (read all statements, grep mathlib for each) | ~25 min | 2 candidates surfaced |
| `le_normalizer_centralizer` discharge | ~12 min | 1 probe iteration to fix `group` import + `linarith`→`trans` |
| `commg_normr` discharge | ~15 min | 1 probe iteration to fix `commutator_def` rewrite scope |

Pattern: **mathlib statement-shape grep is the best ROI play left**
for `CommutatorExtras`-style "missing utility lemma" axioms. Every
discharge that doesn't need new structural infrastructure goes in
one PR for ~12-15 min. The bottleneck is the *next* search-by-shape
sweep finding something proveable — not the proving itself.

## Final state (post-Inc 21)

| Metric                | Post-night (after Inc 19) | After Inc 20-21 |
|-----------------------|---------------------------|-----------------|
| Top-level BG §1 thms  | 17                        | 17              |
| Real axioms           | 18                        | **16**          |
| `sorry` warnings      | 0                         | 0               |
| True-placeholder axs  | 0                         | 0               |
| CommutatorExtras axs  | 3                         | **1** (`commutator_sup_le` remains) |

## Where the next leverage lives

> **Superseded by the seventh-hour update below (Inc 26-27).** The
> "mathlib upstream PR" path is closed per standing decision: no
> upstream from this worktree. Kept for historical context.

The two paths forward (as of Inc 21):

1. ~~**Build mathlib bricks upstream.** Fitting subgroup + pCore as
   the first PR. Discharging ~5 of the 16 remaining axioms cascades
   from these two definitions alone.~~ **Closed:** standing decision
   is no mathlib upstream from this worktree. Fitting/pCore bricks
   would have to land via a different path (or be inlined locally,
   which defeats the leverage premise).
2. **Structural decomposition (handoff options 6, 7).** Adds new
   theorems but also new leaves/axioms. Net axiom count likely goes
   up not down, which trades raw count for proof tree completeness.

Both were real work, ~hours each. The 12-15-min-per-axiom regime
was genuinely over for what `CommutatorExtras` could offer.

# Update — seventh hour: structural relativization (Inc 26-)

Picked HANDOFF option 4 (P1_10 soundness refactor) as the next move
after the sixth-hour sweep exhausted shape-discharge candidates. The
refactor needs the 1.9-base axiom at level `K = N_G(C_G(A))`, which
the original Inc 16 axiom hardcoded to `K = ⊤`. Splitting into two
increments:

**Inc 26** — Relativize the base axiom.
- New `IsStableFactor' A K H` struct (was `IsStableFactor A H` with
  K = ⊤ baked in). The `conjStable` clause expresses K-normality of H
  pointwise rather than via `(H.subgroupOf K).Normal` — keeps
  everything in `Subgroup G`, matches MathComp.
- New axiom `stable_factor_cent_chain'` at arbitrary K.
- Old `stable_factor_cent_chain` (K = ⊤) is now a **theorem** derived
  from the relativized axiom via `Subgroup.card_top` + the
  `Normal.conj_mem ↔ conjStable` translation.
- Public API (`BGsection1.lean`) unchanged — same theorem signature.

Net axiom count effect: ±0 (one axiom removed, one added). The win
shows up in Inc 27, which uses the new K-parametric axiom to discharge
the false-claim `stable_factor_data` in P1_10.

Why this is "broaden-then-dig" not "dig narrow": the per-axiom sweep
(Inc 20-21) was exhausted. The next leverage was a structural change
that unblocks *two* things — P1_10 soundness fix AND P1_9 list
induction (future Inc 28). The relativization is the shared dependency,
not a piecemeal discharge.

Pattern note: when a base axiom hardcodes a parameter that downstream
work needs to vary, the right move is to relativize the base + derive
the specialization, not to add a parallel axiom. The K = ⊤ theorem
is a one-screen proof from the relativized axiom — cheap.

**Inc 27** — P1_10 soundness fix.
- Removed false-claim `stable_factor_data` axiom (asserted
  `(centralizer A).Normal` in G without `A.Normal` — not true in general).
- Replaced with `comm_norm_cent_subset_cent` axiom citing
  `BGsection1.v:422-425` (the MathComp `comm_norm_cent_cent` +
  intersect-normalize chain at the specific (N_G(C), A, C) instantiation).
- The `hSelfCent` hypothesis is now load-bearing — it's what makes the
  axiom statement mathematically true.
- Rerouted the proof via `N := N_G(C)`: apply the relativized 1.9-base
  (Inc 26) at K = N, then collapse `N = C` and `C = ⊤` using mathlib's
  `normalizerCondition_of_isNilpotent`.

Net axiom count: ±0 again (false axiom out, cited axiom in). But the
underlying P1_10 statement is now soundly proved.

Combined Inc 26 + Inc 27 result: 13 axioms (unchanged), but the
`stable_factor_data` soundness issue (HANDOFF option 4) is closed.

## Where leverage lives now (post-Inc 27, 2026-05-27)

Per-axiom inline discharge is exhausted (the original "Where the next
leverage lives" analysis above stands, minus the upstream-PR option).
Real candidates for the FT-port direction:

1. **`series_cent_of_stable` list induction (Inc 28 candidate).**
   The relativized 1.9-base from Inc 26 was specifically designed to
   unblock this. P1_9's list induction is now tractable — pick up
   the recursion that previously required a hardcoded K = ⊤.
2. **Structural decomposition (HANDOFF options 6, 7).** Still
   available. Trades raw axiom count for proof-tree completeness.

Off the table:
- ~~Mathlib upstream PRs (Fitting + pCore).~~ Standing decision: no
  upstream from this worktree.
- Per-axiom 12-15-min sweeps. Genuinely over.

Parallel track to consider:
- **CFSG scaffolding** (`FiniteSimpleGroups/`) is now in motion as
  of Inc 28. See the CFSG-track section of root `HANDOFF.md` for
  state. Sometimes the right move is to push CFSG forward rather
  than chip at FT-port axiom 14.

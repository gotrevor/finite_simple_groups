# ▶ ACTIVE SESSION HANDOFF (2026-05-30)

**Branch:** `cfsg-fitting-nilpotent` (off `main` @ `e1a7f88`, **not pushed** — local only)

**What changed:** Three axiom-free bricks toward discharging `axiom
fittingSubgroup_isNilpotent` (CFSG track), via mathlib's finite-nilpotency TFAE
route (no `pCore` in mathlib, so built by hand). All in
`FiniteSimpleGroups/FittingSubgroup.lean`; build green throughout
(`lake build FiniteSimpleGroups.FittingSubgroup` → EXIT 0, 8249 jobs, no sorry):
- `1a4a31e` — `sylow_characteristic_of_isNilpotent` + `sylow_normal_of_normal_nilpotent`
  (roadmap step 1).
- `5f2e9c8` — `normal_pgroup_le_fittingSubgroup`: a normal p-subgroup is ≤ `F(G)`
  (roadmap step 3).
- `ec9a125` / `5f9c2a1` — `docs/fitting-roadmap.md` (route + refined step-2 plan).

**Roadmap steps 1 and 3 done. Step 2 (the hand-rolled p-core) is the bottleneck
and next target:** define `Op G p := sSup {Q | Q.Normal ∧ IsPGroup p Q}` and
prove it normal + a p-group. The p-group half is a `Finset.sup` induction over
the (finite) index set, stepped with `IsPGroup.to_sup_of_normal_right`, carrying
normal+p-group jointly as the motive. ⚠️ No direct `sSup`-of-normals lemma exists
in mathlib v4.29.1 — see roadmap for the plan. Budget a focused session; needs
several reliable edit-build cycles.

**PR-body draft:**
> **CFSG: first verified bricks toward Fitting's Theorem**
> Begins discharging `fittingSubgroup_isNilpotent` (a cited axiom) via
> `isNilpotent_of_finite_tfae`. mathlib lacks a group-theoretic `pCore`, so the
> decomposition is hand-built. Adds `sylow_characteristic_of_isNilpotent` (Sylows
> are characteristic in a finite nilpotent group) and `sylow_normal_of_normal_nilpotent`
> (Sylow of a normal nilpotent `N ⊴ G` is normal in `G`, via
> `ConjAct.normal_of_characteristic_of_normal`). Both axiom-free; single-target
> build green. Remaining 3 steps in `docs/fitting-roadmap.md`.

---

# HANDOFF — finite_simple_groups-ft repo 🪜

> **Read this first.** This repo now hosts **two parallel tracks** in one worktree:
>
> 1. **FT-port** (`FeitThompson/`) — Coq/MathComp port of the Feit-Thompson §1 chapter into Lean. See [`FeitThompson/HANDOFF.md`](FeitThompson/HANDOFF.md) for FT-track state. Per-axiom discharge is exhausted as of Inc 27; per [`FeitThompson/findings.md`](FeitThompson/findings.md) "Where leverage lives now", the next FT-track move is either Inc 28 (`series_cent_of_stable` list induction) or structural decomposition.
> 2. **CFSG-track** (`FiniteSimpleGroups/`) — Classification of Finite Simple Groups scaffold. Started life as an A_n scratch-build (see "Historical: A_n simple" section below); pivoted at Inc 28 to parameterized Lie-type / Sporadic carriers + tightened `IsClassified` disjuncts. See the **CFSG-track** section directly below.
>
> Standing decisions:
> - **No mathlib upstream PRs from this worktree.**
> - **Admin-merge cadence** on green CI (same convention for both tracks, established by FT-port PRs #35-#40 and inherited by CFSG PR #41).

---

## CFSG-track state (as of Inc 28, 2026-05-27)

**Files** in `FiniteSimpleGroups/`:

| File | Lines | Role |
|------|-------|------|
| `LieType.lean` | 114 | Parameterized `PSL n q`, `PSU`, `PSp`, `POmega` + `classicalLieTypeCarrier` lookup |
| `Exceptional.lean` | 168 | 10 exceptional Lie-type families (`G2 q`, `F4 q`, `E6_q q`, ..., `²B2 q`, etc.), each parameterized + simplicity axioms + `exceptionalLieTypeCarrier` lookup |
| `Sporadics.lean` | 222 | 26 sporadic groups as opaque types + `Name.carrier : Name → Type` lookup (uses `_root_.` qualification to dodge constructor-name collisions) |
| `Classification.lean` | 80 | `IsClassified G` disjunction over (cyclic prime / A_n / classical Lie-type / exceptional / sporadic), each quantifying over carrier types via `Nonempty (G ≃* …)` |
| `Alternating.lean` | 527 | Historical scratch-build (see below) — 3 leaf sorries, retired as a contribution path |
| `Cyclic.lean`, `Basic.lean`, `SmallOrders.lean`, `ProofStrategy.lean` | — | Older scaffold pieces from the A_n era; partly still wired |

**Inc 28 PR** ([#41](https://github.com/gotrevor/finite_simple_groups/pull/41)) — merged 2026-05-27 admin. What it changed:

- `PSL`, `PSU`, etc. went from `opaque PSL : Type` (one Lean type, simplicity axioms vacuously universal) to `opaque PSL (n q : ℕ) : Type` with real per-parameter quantification. The Inc 27 vacuity bug is fixed.
- Exceptional families gained simplicity axioms (none before).
- `IsClassified` disjuncts dropped the `opaque … : Prop` empty-proposition routing; they now express the real classification via `Nonempty (G ≃* carrier …)`.

**What's NOT done** (open Inc 29+ candidates):

- Carrier types are still opaque. No connection to mathlib analogues yet (e.g., `PSL 2 q` ↔ `SL(2, F_q)` quotient). Each `classicalLieTypeCarrier` and `exceptionalLieTypeCarrier` returns an opaque type with axiom-only `IsSimpleGroup` witness.
- No equivalences between sporadic Name enum and concrete sporadic constructions (most don't exist in mathlib anyway).
- `Alternating.lean` scratch-build still wired but contributes only 3 unproved sorries; not part of `IsClassified` per the upstream-shipped pivot.

**Original HANDOFF (A_n scratch-build) is preserved as historical context below.** It's still accurate for the A_n side but is no longer the primary direction of this repo.

---

## Historical: A_n simple — upstream landed before us

> The section below was rewritten 2026-05-25 after a session discovered that everything below was working toward a target that no longer exists. Previous versions recommended translating from mathcomp; that recommendation was empirically wrong and is retracted.

## TL;DR

1. **`alternatingGroup.isSimpleGroup` for `5 ≤ Nat.card α` is already in mathlib master.** Antoine Chambert-Loir, PR #36524, merged ~2026-04. File: `Mathlib/GroupTheory/SpecificGroups/Alternating/Simple.lean:201`. Strategy: Iwasawa criterion (action-theoretic), not cycle decomposition.
2. **Mathcomp's `simple_Alt5`** (`solvable/alt.v:394`) also uses an action-theoretic proof (2-transitive → primitive + Sylow base + induction via point-stabilizer). Mathcomp has **no commutator-with-3-cycle leaf lemmas** to plunder. Translation from mathcomp into our cycle-decomposition scaffold is not possible.
3. **Our scratch-build** (case-by-cycleType skeleton with 3 leaf-witness `sorry`s in `FiniteSimpleGroups/Alternating.lean`) was always a learning exercise. The mathlib PR ambition referenced in earlier HANDOFFs is stale.
4. **The remaining upstream TODO** at `Mathlib/GroupTheory/SpecificGroups/Alternating.lean:57` is the **iff packaging** ("simple iff `Fintype.card α ≠ 4`"). The hard direction is done; what remains is small-n bookkeeping (n=4 not-simple via Klein four, n ≤ 3 edge cases). Probably a few-hour PR.

## What was actually contributed by the scratch-build sessions

- **Proof-tree architecture**: case-by-cycleType skeleton with named cases, axiomatized leaves, real `commutator_mem_normalClosure`, real Case 3 helpers. Pedagogically clean if anyone wants to teach the Galois 1832 proof from a top-down scaffold.
- **Case 2 bug catch**: the textbook "one-step commutator" argument for Case 2 (`g = (a b c)(d e f)`, `τ = (a b d)`) produces a **5-cycle, not a 3-cycle**. Hand-verified. Case 2's witness signature was retyped to be a two-step argument (commutator gives 5-cycle, chain through Case 1).
- **Empirical refutation** of the prior HANDOFF's "translate from mathcomp will be net-faster" claim (which carried 80% confidence on no evidence).

These are real artifacts. The proof of `alternatingGroup_isSimple` in this repo is not.

## State of the files

`FiniteSimpleGroups/Alternating.lean` has **3 sorries**, all in leaf-witness helpers (Case 1, Case 2 retyped, Case 4). Signatures are verified-achievable per hand-verification. Case main theorems and the top-level `alternatingGroup_isSimple` wire through correctly modulo those three sorries.

`commutator_mem_normalClosure` is real proof. Case 3 helpers (`orderOf_g_eq_six_of_3_2_pattern` etc.) are real proof.

## Options for the next session

Pick one based on appetite. None is "the right answer" — that was already taken upstream.

### Option A: Wire to upstream, retire the scaffold

Replace `alternatingGroup_isSimple` with a one-liner using `alternatingGroup.isSimpleGroup`. Mark the case-decomposition files as `/-! Teaching material — for the actual proof see Mathlib... -/`. Honest retirement.

Smallest, cleanest. Loses the learning artifact's pedagogical value if you delete the scaffold; preserves it if you keep the files and just stop trying to close sorries.

### Option B: Port Chambert-Loir's Iwasawa proof

Read `Mathlib/GroupTheory/SpecificGroups/Alternating/Simple.lean` deeply. Replicate the proof here using the same `IwasawaStructure`, `IsPreprimitive`, `powersetCard` action machinery. Real practice with the upstream technique — the case-decomposition skeleton in this repo doesn't touch any of it.

Higher-leverage learning than scratch-building leaves. Probably the most-useful-skill-per-hour next step.

### Option C: Take the small iff TODO upstream

The `Alternating.lean:57` TODO asks for the iff version (`simple ↔ card ≠ 4`). Hard direction is shipped; what's missing is small-n cases: n=4 is not simple (Klein four obstruction), n ≤ 3 are edge cases. Translate `not_simple_Alt_4` from mathcomp (the proof structure transfers — it's a Sylow + Klein-four argument), wire small-n cases.

Estimated few-hour PR. Smaller and more bookkeeping-heavy than the original scaffold goal, but a real mathlib contribution.

### Option D: Keep scratch-building the 3 leaves

Pure exercise value, no upstream destination. The leaves are well-scoped — Case 4-A is the cleanest (`[g, h] = h` identity, free-point sub-case). 2-4 hours of `Equiv.ext` + pointwise commutator work. Honest about being practice.

## Lessons (please read before committing this session's work)

- **Check current state of the target before claiming "still a TODO".** The KB doc that motivated the scaffold (`claude/knowledge/core/projects/lean-journey/side-quests/finite-simple-groups.md`) made the "still a TODO" claim without verifying mathlib master. That claim propagated into the original HANDOFF, which then recommended scratch-building. Stale-target diagnosis cost both sessions.
- **WebFetch on raw GitHub gives paraphrased summaries.** Clone the repo and grep — verbatim proof bodies are the whole point in translation work. Lesson saved to user feedback memory.
- **Don't paste textbook arguments without hand-verifying small cases.** The Case 2 bug (one-step commutator gives 5-cycle, not 3-cycle) was in the prior HANDOFF as a "standard" construction. Took pen-and-paper to catch.

## Mathlib pointers (for whoever picks this up)

- `Mathlib/GroupTheory/SpecificGroups/Alternating/Simple.lean` — the actual proof.
- `Mathlib/GroupTheory/SpecificGroups/Alternating.lean:57` — remaining iff TODO.
- `Mathlib/GroupTheory/SpecificGroups/Alternating/KleinFour.lean` — n=4 machinery.
- `Mathlib/GroupTheory/SpecificGroups/Alternating/Centralizer.lean` — adjacent infrastructure.
- `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` — the Iwasawa criterion itself.

## Local clones (if you don't have them)

- `~/src/mathlib4` (shallow clone)
- `~/src/math-comp` (shallow clone) — for reading mathcomp's action proof if curious

---

*Rewritten 2026-05-25 after upstream-shipped discovery. Prior versions recommending mathcomp translation are retracted.*

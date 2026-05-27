# HANDOFF — FT-port experiment (`FeitThompson/`)

**As-of**: 2026-05-26, end of Inc 27
**Branch**: `ft-port-experiment`
**Repo**: `~/src/finite_simple_groups-ft/` → `gotrevor/finite_simple_groups`

> **Note**: This repo hosts TWO parallel workstreams:
> - `FeitThompson/` (this doc) — FT-port experiment, BG §1 from MathComp
> - `FiniteSimpleGroups/` (root `HANDOFF.md`) — A_n simple scratch-build, CFSG learning scaffold
>
> Don't conflate them. Each has its own theme and goals.

## Read this first

The FT-port experiment measures AI-collaborative cost of porting MathComp's
Coq `BGsection1.v` (Bender-Glauberman §1) to Lean. Theme:
**structural decomposition + axiomatize leaves + cite Coq lines**.
Not first-principles proving.

Full session history + cost model: `FeitThompson/findings.md`.
Side-quest doc in Trevor's KB: `claude/knowledge/core/projects/lean-journey/side-quests/finite-simple-groups.md`.

## Current state

| Metric                | Value |
|-----------------------|-------|
| Top-level BG §1 thms  | 17    |
| Real axioms           | **13** |
| `sorry` warnings      | **0** |
| Orphan axioms         | **0** (CI-strict) |
| Dead-True placeholders | **0** (CI-strict) |
| FT-port PRs merged    | 27 (Inc 1-27) |
| Soundness audit       | **clean** (Inc 27 closed the last false-claim axiom) |

All 17 top-level theorems re-exported from `FeitThompson/BGsection1.lean`.
Build green: `lake build FeitThompson`.

## Worktree theme (don't violate)

1. **Zero `sorry` in `FeitThompson/`** — every leaf is either a real
   proof or a named `axiom` with a Coq line citation. `sorry` means WIP;
   `axiom` means scaffolding. See `feedback_axioms_at_leaves.md` memory.
   (The `FiniteSimpleGroups/` scaffold *does* use `sorry` deliberately;
   different theme.)
2. **Cite-then-chain over inline-prove** — when blocked on a missing
   mathlib lemma, push the unknown one level deeper into 2-3 named
   MathComp-cited axioms (Inc 11 pattern) rather than proving inline.
3. **Lean-collapse simplification** — Coq's `G : {group gT}` is our
   `⊤ : Subgroup G`. When the ambient is abelian, many Coq-side proofs
   collapse trivially (Inc 15 pattern).
4. **No True-hypothesis axioms** — `(h : True)` axioms are silently
   unsound. Grep `: True` in any new axiom declarations and refactor.
5. **No orphan axioms or dead-True placeholder theorems** — CI runs
   `FeitThompson/scripts/orphan-axioms.sh --strict` (Inc 23-25). If
   you add a tree-decomposition branch as a separate declaration,
   wire it into a proof in the same PR, or leave it as a comment.
   Don't materialize aspirational structure as code.
6. **Increment style** — one focused PR per increment, merged via
   `gh pr merge <N> --admin --merge` (bypasses the perpetually-queued
   CI runner).

## What got done in Inc 11-19 (autonomous overnight run)

- Inc 11: discharged `coprime_commGid` via 3 new CommutatorExtras bricks
- Inc 12: discharged `pPowerImage_isSubgroup_and_normal` (powMonoidHom+conj_pow)
- Inc 13: added Theorem 1.11, Corollary 1.12, Theorem 1.13 trees
- Inc 14: discharged `exists_prime_pPowerImage_ne_top` (Cauchy chain)
- Inc 15: discharged `inf_bot` (Lean-collapse: abelian → ⁅⊤,A⁆ = ⊥)
- Inc 16: soundness cleanup (3 True-hypothesis axioms removed)
- Inc 17: discharged `Phi_nongen` (mathlib has it as `frattini_nongenerating`)
- Inc 18: discharged `wlog_cyclic` (zpowers argument, 7 lines)
- Inc 19: updated `findings.md` with fifth-hour summary

## What got done in Inc 26-27 (seventh hour, P1_10 soundness fix)

- **Inc 26** — Relativize the 1.9-base axiom.
  - New `IsStableFactor' A K H` struct + `stable_factor_cent_chain'`
    axiom at arbitrary ambient `K` (was K = ⊤ hardcoded).
  - Old `stable_factor_cent_chain` (K = ⊤) is now a derived theorem.
  - Public API in `BGsection1.lean` unchanged.
- **Inc 27** — P1_10 soundness fix (HANDOFF option 4, **CLOSED**).
  - Removed false-claim `stable_factor_data` axiom.
  - Replaced with single cited `comm_norm_cent_subset_cent` axiom
    (MathComp `comm_norm_cent_cent` + intersect-normalize at the
    (N_G(C), A, C) instantiation; `BGsection1.v:422-425`).
  - Reroutes via K = N_G(C); collapses N = ⊤ using mathlib's
    `normalizerCondition_of_isNilpotent`.
  - `hSelfCent` hypothesis is now load-bearing (was unused).

Net axiom count over Inc 26-27: ±0 (one false axiom out, one cited
axiom in for Inc 27; one axiom out, one in for Inc 26). But the
soundness invariant is restored — every axiom in the FT port now
states something mathematically true.

## What got done in Inc 20-25 (sixth hour, sweep + cleanup)

- **Inc 20** — `le_normalizer_centralizer` (`A ≤ N(C(A))`). No mathlib
  analog; provable from `mem_normalizer_iff` + `mem_centralizer_iff` +
  `group` tactic (~15 LOC).
- **Inc 21** — `commg_normr` (`A ≤ N(⁅⊤, A⁆)`). Closure-induction on
  `⁅⊤, A⁆` with a `conj_into` helper (~35 LOC).
- **Inc 22** — docs (findings + HANDOFF refresh).
- **Inc 23** — orphan-axiom audit: removed `norm_C_eq_top`,
  `wlog_comm_eq_top`, `abelian_charsimple_special` (all zero refs,
  leftover from original tree decompositions). Added
  `FeitThompson/scripts/orphan-axioms.sh` detector + soft CI hook.
- **Inc 24** — dead-True placeholder cleanup: removed P1_4's
  `semidirect_solvable`, `piPart_Fitting_trivial`, `fitting_in_G`
  (all `True := by trivial` with zero refs). Extended detector to
  catch this pattern.
- **Inc 25** — promoted detector to **strict** mode in CI (this
  increment). Any future regression fails the build.

**Sweep result**: the other 13 axioms all require infrastructure not
in scope for shape-discharge (see ❌ list under "Next-session options"
below). Don't re-run the full sweep blindly — see the classification
table in `findings.md` sixth-hour update.

## Next-session options (pick one, time-box)

### Sweep-discharged ✅ (do NOT re-attempt)

- Option 2 (`norm_C_eq_top`) — **removed** in Inc 23 as an orphan
  axiom (zero references; the actual P1_10 proof shortcuts via
  `stable_factor_data`). The P1_10 structural refactor (option 4
  below) will need to re-introduce an equivalent intermediate; that's
  fine, the orphan removal doesn't pre-empt the refactor.
- Option 3 (axiom shape sweep) — completed Inc 20-21. Two wins, then
  exhausted. Remaining axioms classified in `findings.md` sixth-hour.

### Blocked on missing mathlib bricks ❌ (skip until brick lands)

- **`commutator_lt_of_minnormal` (L1_2)** — needs Fitting's theorem
  (F(G).IsNilpotent). Blocked on the upstream-Fitting-subgroup PR.
- **P1_3 axioms** (`cent_Fitting_le_chief_stab_of_in_Fitting`,
  `chief_stab_sub_Fitting`) — Hall theory / chief factor machinery.
- **`coprime_trivg_cent_Fitting_cyclic` (P1_4)** — needs semidirect
  product machinery (G ⋊ A construction).
- **Quotient-action axioms** (`coprimeR_cent_prod`,
  `coprime_cent_Phi_chain`, `stable_factor_cent_chain`,
  `series_cent_of_stable`) — need `quotient_cents2`, `quotientSGK`
  family of lemmas; not in mathlib.
- **`abelian_charsimple_special`, `nontrivial_assembly` (T1_11)** —
  Aschbacher 24.7 / charsimple-special structure.
- **`critical_subgroup_exists` (T1_13)** — Thompson critical subgroup
  via group cohomology.
- **`corollary_assembly` (C1_12)** — bundled via 1.10 + 1.11 + OhmE.
- **`wlog_comm_eq_top` (T1_11)** — packaged 1.6(a)+1.6(b) reduction.
- **`commutator_sup_le` (CommutatorExtras)** — MathComp `commMG` sup
  distribution. Inc 11 Phase 1 blocker; flagged off-ramp.

### Deep (refactor) — only if you have ~hours

**4. ~~`stable_factor_data` (P1_10) latent soundness issue~~** —
**CLOSED in Inc 27.** The P1_10 proof now routes through `N := N_G(C)`
using the relativized 1.9-base (Inc 26) + mathlib's
`normalizerCondition_of_isNilpotent`. The replacement axiom
`comm_norm_cent_subset_cent` (MathComp `comm_norm_cent_cent` chain)
is the new leaf. A future increment could inline-prove it by adding
`comm_norm_cent_cent` to `CommutatorExtras` (~50 LOC mirror of
`solvable/commutator.v:293`).

**5. `series_cent_of_stable` (P1_9)** — list induction discharge.
The Inc 26 relativized 1.9-base now makes this tractable: the list
induction can step through intermediate subgroups (not just ⊤). Still
~hours of bookkeeping for the `last_ind`-style structural induction.
Net axiom count drops by 1.

### Wide (structural decomposition) — adds new axioms

**6. Lemma 1.14 (4 sub-lemmas)** — coprime quotient pgroup normalizer /
centralizer. Needs quotient-group infrastructure (`G ⧸ M` for `M.Normal`).
Coq lines 567-614. Each sub-lemma can be a tree with the quotient
construction packaged as an axiom. **Net axiom count goes UP** but
proof-tree breadth increases.

**7. Props 1.15a, 1.15b, 1.16** — denser p-local machinery. 1.15a
(solvable_p_constrained) needs `pcore_normal`. 1.16 uses bigUnion of
centralizers over cyclic quotients — heavy.

### Better strategic move (per `findings.md` Hour 2 / Hour 4)

**Build the Fitting subgroup mathlib PR upstream.** Discharges ~5 of
the 16 remaining axioms cascade-style (Fitting nilpotence unblocks
L1_2; pCore unblocks P1_3, T1_11 chain). The "build bricks" strategy
was the recommendation from earlier hours and is still the highest-
leverage move once the cheap inline discharges are gone.

## Workflow reminders

- **Build**: `cd ~/src/finite_simple_groups-ft && lake build FeitThompson` (~30s clean, <5s incremental)
- **Single file**: `lake build FeitThompson.BGsection1.P1_X`
- **Axiom count**: `grep -rcE "^axiom [a-zA-Z_]" FeitThompson/ | grep -v ':0$' | awk -F: '{s+=$2} END {print s}'`
- **PR pattern**:
  ```
  git add <files> && git -c commit.gpgsign=false commit -m "Increment N: ..."
  git push
  gh pr create --base main --head ft-port-experiment --title "..." --body "..."
  gh pr merge <N> --admin --merge
  ```
- **Pull main first** — the parallel `FiniteSimpleGroups/` workstream merges
  to main on its own branches (`wire-up-todo-comment`, etc.). Always start
  a session with `git fetch origin && git merge origin/main` to avoid
  conflicts. Touch only `FeitThompson/` files (and this file).
- **No upstream PRs** — Trevor doesn't want anything submitted to mathlib
  itself from this worktree (decision 2026-05-26: "build my own stuff
  independently"). Stay local.

## What NOT to do

- ❌ Don't submit to mathlib upstream — local-only by Trevor's preference
- ❌ Don't touch `FiniteSimpleGroups/` — different workstream, see root HANDOFF
- ❌ Don't touch `~/src/bounded_gaps/` — different parallel session
- ❌ Don't introduce `sorry` in `FeitThompson/` — zero-sorry invariant
- ❌ Don't add `axiom ... (h : True) : ...` — silently unsound
- ❌ Don't refactor the Coq source — `papers/odd-order/` is vendored, read-only
- ❌ Don't try to formalize CFSG itself — this is BG §1 port, scoped

## Useful refs

- `papers/odd-order/BGsection1.v` — source of truth (1335 lines, 89 declarations)
- `FeitThompson/findings.md` — full session log with cost model
- `FeitThompson/CommutatorExtras.lean` — 3 MathComp-cited bricks (Inc 11)
- `FeitThompson/MathlibStubs.lean` — local stubs (pCore, FittingSubgroup,
  IsAbelem, MinNormal, IsHall, IsChiefFactor, pCoreLayer)
- `mathlib-prs/FittingSubgroup.md` — scoped (but not started) mathlib PR
  for the biggest unblock

## Memory pointers (Trevor's KB)

- `reference_lean_tactics_gotchas.md` — accumulated Lean 4 / mathlib v4.29.1
  gotchas; updated 2026-05-25/26 with `frattini_nongenerating`, zpowers
  patterns, `powMonoidHom`, True-axiom audit
- `feedback_axioms_at_leaves.md` — the zero-sorry / axioms-at-leaves principle
- `user_compelling_problems.md` — Trevor's compelling-problem filter (BB,
  FLT, FSG, prime pairs, Collatz) — useful when picking what to discharge

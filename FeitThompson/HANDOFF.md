# HANDOFF — FT-port experiment (`FeitThompson/`)

**As-of**: 2026-05-26, end of Inc 19
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
| Real axioms           | 18    |
| `sorry` warnings      | **0** |
| True-placeholder axs  | **0** |
| FT-port PRs merged    | 19 (Inc 1-19) |

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
5. **Increment style** — one focused PR per increment, merged via
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

## Next-session options (pick one, time-box)

### Deep (axiom discharge) — easy wins likely

**1. `commutator_lt_of_minnormal` (L1_2)** — `⁅M, F(G)⁆ < M` for
minnormal M. Needs F(G) nilpotence + meet_center_nil. ~1 hr if mathlib
has the right pieces. **First check**: grep mathlib for `meet_center`
or "subgroup of nilpotent meets center nontrivially".

**2. `norm_C_eq_top` (P1_10)** — uses MathComp's `nilpotent_sub_norm`
("every proper subgroup of nilpotent G has strictly larger normalizer").
Mathlib has `NormalizerCondition` and `normalizerCondition_of_isNilpotent`
(`Mathlib/GroupTheory/Nilpotent.lean:877`). Might be a direct discharge
similar to Inc 17's Phi_nongen win.

**3. Search-by-statement-shape pass over all 18 axioms** — Inc 17 found
`Phi_nongen` ↔ `frattini_nongenerating` literally in mathlib. There
are probably more. For each axiom, grep mathlib for the statement
shape rather than the name. ~30-60 min for a full sweep.

### Deep (refactor needed)

**4. `stable_factor_data` (P1_10) latent soundness issue** — claims
`(centralizer A).Normal` without `A.Normal`. False in general. Fix
requires P1_10 structural refactor to track `N_G(C_G(A))` rather than
collapsing to `⊤`. Bigger work, ~2-3 hr.

**5. `series_cent_of_stable` (P1_9)** — list induction discharge. Needs
~30-60 min of Lean-side list bookkeeping (`List.reverseRecOn` or
strong induction over indices). Doable but fiddly.

### Wide (structural decomposition)

**6. Lemma 1.14 (4 sub-lemmas)** — coprime quotient pgroup normalizer /
centralizer. Needs quotient-group infrastructure (`G ⧸ M` for `M.Normal`).
Coq lines 567-614. Each sub-lemma can be a tree with the quotient
construction packaged as an axiom.

**7. Props 1.15a, 1.15b, 1.16** — denser p-local machinery. 1.15a
(solvable_p_constrained) needs `pcore_normal`. 1.16 uses bigUnion of
centralizers over cyclic quotients — heavy.

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

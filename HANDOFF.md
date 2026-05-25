# HANDOFF: closing the Galois sub-cases 🪜

Trevor's framing for whoever picks this up (human or AI):

> Lean into really fractal theorems — top down. Lots of sorries — ultimately, the sorries drop like flies. **Pretty at the top, ugly in the details (smooth-brained).**

This file is the smooth-brained playbook for finishing `Alternating.lean`'s 4 remaining sub-case sorries.

## The principle

Don't try to write elegant leaf proofs. The structural decomposition at the top should be clean and obviously correct. The leaves can be brute force, `decide`, `aesop` spam, helper sub-lemmas with their own sorries — whatever works to make the bytes compile.

`sorry` is **structure**, not failure. Use it freely while shaping the proof tree.

The progression to follow for any sub-case:

1. **Write a 5-10 line proof outline of the top-level statement** that mentions ONLY clean intermediate lemmas. Each intermediate is `sorry`.
2. **Build it.** If the top-level type-checks against your sorried intermediates, the structure is right.
3. **Now attack each intermediate.** Repeat — decompose into sub-sub-lemmas, sorry them, build, descend.
4. **At the bottom**, when sub-sub-sub-lemmas are one-line statements about specific cardinalities or membership, drop the elegance entirely. Try `decide`, `native_decide`, `omega`, `aesop`, `simp [...]` with a long list. Anything goes.

**Lean in harder than a human might.** A human Lean prover often tries to find the "right" lemma. The smooth-brained approach is: don't. Build any chain that works. Refactor never.

## The four sub-cases

All four live in `FiniteSimpleGroups/Alternating.lean` between the `GaloisReduction` namespace markers. The top-level dispatcher `exists_threeCycle_of_normal` already type-checks against them.

### Case 3 sub-case B (closest to done) — `(g^2).IsThreeCycle`

Already partially handled: sub-case A (`g` is itself a 3-cycle) is closed. The remaining sub-case B is when `g.cycleType = {3, 2, 2, ..., 2}` with at least one 2.

Suggested fractal decomposition:

```lean
-- Top of the proof tree (clean):
refine ⟨g^2, ?_, Subgroup.zpow_mem (Subgroup.mem_zpowers g) 2⟩
show (↑(g^2) : Equiv.Perm (Fin n)).IsThreeCycle
-- Now reduce to card support = 3:
rw [← card_support_eq_three_iff]
-- Now ugly leaf:
exact card_support_g_sq_eq_three g h_one_three h_rest_swap h_no_swaps_neg
-- where card_support_g_sq_eq_three is a separate `sorry`-laden helper.
```

Then for `card_support_g_sq_eq_three`, decompose into:
- `orderOf_eq_six` : `orderOf g = 6` (from `lcm_cycleType` + arithmetic on `{3, 2, 2, ...}`)
- `g_sq_pow_three_eq_one` : `(g^2)^3 = 1` (from `g^6 = 1`)
- `cycleType_g_sq_repl` : `(g^2).cycleType = Multiset.replicate k 3` (via `cycleType_of_pow_prime_eq_one`)
- `k_eq_one` : `Multiset.card (g^2).cycleType = 1`
  - From `sum_cycleType`: `3k = card support (g^2)`
  - From `support_pow_le`: `support (g^2) ⊆ support g`
  - From `sum_cycleType`: `card support g = 3 + 2 * (h_rest_swap count)`
  - Argue `k = 1` by interval_cases + omega.

Each of these intermediate lemmas can have an ugly proof. They're all true; the proof shape is mechanical.

### Case 1 (long cycle, commutator) — `(g h g⁻¹ h⁻¹).IsThreeCycle`

`g` has a cycle of length `≥ 4`. Pick the first three points `a, b, c` of that cycle (concretely: use `cycleOf g x` for `x ∈ support g` with cycle length `≥ 4`; extract three points).

Take `h := Equiv.swap a b * Equiv.swap b c` (the 3-cycle `(a b c)`).

The commutator `g * h * g⁻¹ * h⁻¹` is the 3-cycle.

Decompose to:
- `exists_three_points_in_long_cycle` : extract `a, b, c` distinct, all moved by `g`, with `g a = b ∨ g b = c` (i.e., consecutive in the cycle).
- `h_is_three_cycle` : `(swap a b * swap b c).IsThreeCycle` (via `card_support_eq_three_iff` + `decide`-ish argument on support).
- `commutator_eq_explicit_three_cycle` : `g * h * g⁻¹ * h⁻¹ = swap _ _ * swap _ _` for specific points (work out the computation; can use `Equiv.ext` + per-element calculation).
- `commutator_mem_normalClosure` : `g * h * g⁻¹ * h⁻¹ ∈ Subgroup.normalClosure ({g} : Set _)` (immediate from normality).

The "ugly leaf" here is `commutator_eq_explicit_three_cycle` — multi-line `Equiv.ext` with per-element `simp [Equiv.swap_apply_def]` + arithmetic. Don't try to make it pretty.

### Case 2 (multiple 3-cycles, commutator) — same shape as Case 1

`g` has `≥ 2` three-cycles. Extract `(a b c)` and `(d e f)` from `cycleFactorsFinset`. Take `h := (a b d)`. Commutator is a 3-cycle.

Decompose similarly to Case 1.

### Case 4 (only 2-cycles, commutator) — same shape

`g` has only 2-cycles (and an even number of them, since g is even). Since `n ≥ 5` and `g` moves at most `2k` points with `k ≥ 2`, find a free point `e` not in `support g`. Take `h := (a b e)` where `(a b)` is one of `g`'s 2-cycles. Commutator is a 3-cycle.

Decompose similarly.

## Mathlib lemmas worth knowing

Already used in `Alternating.lean`:
- `IsThreeCycle.alternating_normalClosure` — given a 3-cycle in `A_n`, its normal closure is `⊤`.
- `closure_three_cycles_eq_alternating'`
- `Subgroup.normalClosure_le_normal`
- `alternatingGroup.nontrivial_of_three_le_card`

For the sub-cases:
- `Equiv.Perm.cycleType` — `Multiset ℕ` of cycle lengths
- `Equiv.Perm.IsThreeCycle` (= `cycleType = {3}`)
- `card_support_eq_three_iff : #σ.support = 3 ↔ σ.IsThreeCycle`
- `sum_cycleType : σ.cycleType.sum = #σ.support`
- `cycleType_of_pow_prime_eq_one : σ^p = 1 → σ.cycleType = Multiset.replicate _ p` (for `p` prime)
- `pow_prime_eq_one_iff : σ^p = 1 ↔ ∀ c ∈ σ.cycleType, c = p`
- `Equiv.Perm.IsCycle.cycleType` — for a single cycle, `cycleType = {#support}`
- `Disjoint.cycleType_mul` — cycleType of disjoint product is sum
- `Equiv.Perm.support_pow_le` (probably) — support of σ^k ⊆ support σ
- `Equiv.Perm.cycleFactorsFinset` — the disjoint cycle decomposition
- `Subgroup.zpowers`, `Subgroup.zpow_mem`, `Subgroup.mem_zpowers`
- `Equiv.swap_apply_def`, `Equiv.swap_apply_left`, `Equiv.swap_apply_right`

## What's intentionally missing from mathlib v4.29.1

- General `cycleType (σ^k)`. Work around via `cycleType_of_pow_prime_eq_one` plus support arguments.
- Explicit `commutator_eq` lemmas for specific cycle types. Either build small helpers or just unfold `Equiv.ext` and grind per-element.

## Brute-force tactics worth trying liberally

- `decide`, `native_decide` — for any decidable goal over `Fin n`. (`Fin 5`, `Fin 6` small enough that `decide` often closes things.)
- `aesop` — general automation; surprisingly effective on Subgroup membership.
- `omega` — Nat / Int arithmetic. Use everywhere.
- `simp [...]` with a long list of `Equiv.swap_*`, `Subgroup.mem_*`, cycle lemmas.
- `interval_cases` after bounding a Multiset count.
- `Finset.ext` then `decide` for support equalities on small `Fin n`.

## The smooth-brained checkpoint

When you're tempted to clean up a leaf proof, ask: **does the top-level statement still type-check?** If yes, ship it. The leaf can be ugly. The reader of the scaffold sees the clean top; they don't care about the rubble underneath.

## Mathlib PR ambition (if you close all 4)

If all four sub-cases close, the dispatcher (`exists_threeCycle_of_normal`) becomes a real proof. The natural upstream PR is then:

```
theorem alternatingGroup.isSimple_of_card_ne_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (h : Fintype.card α ≠ 4) :
    IsSimpleGroup (alternatingGroup α)
```

This is the documented TODO at the top of `Mathlib/GroupTheory/SpecificGroups/Alternating.lean`. The mathlib reviewers know it's expected and supporting machinery is in place.

After landing upstream, `FiniteSimpleGroups/Alternating.lean` collapses to a one-line re-export, and this whole scaffold's `Alternating.lean` sorry-count goes to 0.

Smooth-brain reward: the most architecturally beautiful possible outcome.

---

*Written 2026-05-25, post-PR #4. State of the scaffold at this point: 6 real-TODO sorries (4 here + 2 in Adjacent/PrimeMul, SmallOrders), 12 axioms, 950 LOC.*

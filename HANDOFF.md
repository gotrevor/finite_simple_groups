# HANDOFF: closing the Galois leaf witnesses 🪜

Trevor's framing for whoever picks this up (human or AI):

> Lean into really fractal theorems — top down. Lots of sorries — ultimately, the sorries drop like flies. **Pretty at the top, ugly in the details (smooth-brained).**

After PRs #11, #13, #14, #16, the Galois proof tree has been pushed down to leaf-witness level. The dispatcher is real proof; the case main theorems are real proof; the **leaf witnesses** are the only sorries — with **corrected and verified signatures**.

## 🚨 Strong recommendation for the next session: TRANSLATE FROM MATHCOMP

Everything in `FiniteSimpleGroups/Alternating.lean` so far has been built from scratch against textbook arguments. This is how the Case 2 bug slipped in: the old HANDOFF's recommended construction was simply wrong (gives 5-cycle, not 3-cycle), and nobody caught it until I sat down with pen and paper.

**A_n simple is fully formalized in mathcomp** as a prerequisite for the Gonthier Feit-Thompson proof. The proof lives somewhere around `mathcomp/solvable/alt.v` or `mathcomp/perm/perm.v` (the same library family already partially translated for FT in the `-ft` worktree). The structural decomposition (cases 1–4), the cycle-extraction lemmas, and especially the **commutator computations** are all already worked out — and mathcomp's `perm_on` / `cycle_decompose` / ssreflect automation makes the commutator pointwise checks dramatically shorter than what mathlib forces you to write by hand.

**Suggested next-session workflow:**
1. Locate the mathcomp proof of `alt_simple` (or the equivalent name). Likely candidates: `mathcomp/solvable/alt.v`, `mathcomp/perm/alt.v`, or a section of `mathcomp/solvable/finmodule.v`. Reading the prerequisite chain (~50–200 lines total) gives the full proof skeleton.
2. For each leaf below, identify the mathcomp lemma(s) it corresponds to and the intermediate facts they call. Note which intermediates already exist in mathlib vs. need to be ported.
3. Translate proof-step-by-proof-step (not line-by-line). The structural casework will land cleanly into my existing scaffold; only the leaf-level commutator computations need fresh Lean code.
4. The FT side in the `-ft` worktree (translating `papers/odd-order/BGsection1.v`) is already doing exactly this pattern. Same workflow applies here.

Confidence ~80% that translation is net-faster than continuing from scratch. The Case 2 bug is the empirical evidence: a translator catches it for free because mathcomp's proof is sound; a scratch-builder doesn't.

## State of the scaffold (post-current-PR)

`FiniteSimpleGroups/Alternating.lean` has **3 sorries**:

1. **`case1_commutator_witness`** — produce a 3-cycle `h_perm` such that the commutator with `g_perm` is also a 3-cycle. Verified achievable: construction is `h = (a b c)` from three consecutive points of the long cycle; `[g, h] = (a b d)`.
2. **`case2_long_cycle_witness`** *(retyped)* — produce an intermediate `g' ∈ NC({g})` with a long cycle. Case 2's main theorem chains this with `exists_threeCycle_of_long_cycle` (Case 1). Verified achievable: take `g' := [g, (a b d)]`; for `g = (a b c)(d e f)` this gives the 5-cycle `(a d c e b)`.
3. **`case4_commutator_witness`** — produce a 3-cycle `h_perm` such that the commutator with `g_perm` is also a 3-cycle. Has two sub-cases:
   - **Free point exists**: `h = (a b c)` where `(a b)` is a 2-cycle of `g` and `c` is the free point. The commutator `[g, h] = h` itself (verified by hand-computation).
   - **No free point** (e.g., `n = 8` with 4 swaps): no direct one-step construction; needs reduction (commutator with `(a b c)` gives an element of cycleType `{2, 2}` with smaller support, then recurse).

## What changed in this PR

- **Case 2's signature was wrong** in the prior scaffold. The old HANDOFF claimed the standard `τ = (a b d)` construction made `[g, τ]` a 3-cycle, but it actually produces a 5-cycle. Hand-verification:
  ```
  g = (a b c)(d e f),  τ = (a b d)
  [g, τ] sends a→d, b→a, c→e, d→c, e→b, f fixed
  trace: a → d → c → e → b → a   ⇒ 5-cycle
  ```
  Case 2's witness is now retyped to produce a long-cycle intermediate, and Case 2's main theorem chains it with Case 1.
- **Case 4 documentation now reflects the verified construction.** With free point `c`, the key identity is `[g, h] = h` (because `g` conjugates `h` to `h⁻¹`, and `h⁻¹ * h⁻¹ = h` since `h` has order 3).

## The principle (unchanged)

`sorry` is **structure**, not failure. Use it freely while shaping the proof tree. **Lean in harder than a human might.** Build any chain that works.

## How to close each leaf

### `case1_commutator_witness`

Construction (verified):
1. Extract `σ_long ∈ g_perm.cycleFactorsFinset` with `σ_long.support.card ≥ 4`.
2. Pick `a ∈ σ_long.support`; set `b := σ_long a`, `c := σ_long² a`, `d := σ_long³ a`.
3. Show `a, b, c, d` pairwise distinct (uses `orderOf σ_long = σ_long.support.card ≥ 4`).
4. Define `h_perm := swap a b * swap b c`; this is `(a b c)`, a 3-cycle by `isThreeCycle_swap_mul_swap_same`.
5. Show `(g_perm * h_perm * g_perm⁻¹ * h_perm⁻¹).IsThreeCycle`.

For step 5, the cleanest path uses the disjoint commutativity reduction:
- `g_perm = σ_long * rest` with `rest` disjoint from `σ_long`'s support (and hence disjoint from `h_perm`'s support).
- `[g_perm, h_perm] = [σ_long, h_perm]` (rest commutes with both σ_long and h_perm).
- Then `[σ_long, h_perm] = (a b d)` by Equiv.ext + per-element computation.

### `case2_long_cycle_witness` (retyped)

Construction (verified):
1. Extract two distinct 3-cycle factors `c₁, c₂ ∈ g.cycleFactorsFinset` with `cᵢ.support.card = 3`.
2. Pick `a, b, c` from `c₁.support` and `d, e, f` from `c₂.support`.
3. Take `τ := swap a b * swap b d` (3-cycle `(a b d)`).
4. Set `g' := g * τ * g⁻¹ * τ⁻¹` (commutator).
5. Show `g' ∈ NC({g})` via `commutator_mem_normalClosure`.
6. Show `(g' : Equiv.Perm _).cycleType` contains a `5`.

For step 6: `g'` is the 5-cycle `(a d c e b)` (assuming `g = (a b c)(d e f) * rest` with `rest` disjoint). Hand computation. The Lean argument can use `Equiv.ext` + per-element verification.

### `case4_commutator_witness`

**Sub-case A (free point exists):**
1. Extract a 2-cycle factor `c₀ ∈ g_perm.cycleFactorsFinset` (via `card_support_eq_two ↔ IsSwap`, mathlib `Equiv.Perm.card_support_eq_two`).
2. Get `a, b` with `c₀ = swap a b`, `a ≠ b`.
3. Get free point `c ∉ g_perm.support` (uses `g_perm.support.card < n`).
4. Define `h_perm := swap a b * swap b c`.
5. Show `h_perm.IsThreeCycle` via `isThreeCycle_swap_mul_swap_same` (needs `a ≠ b`, `a ≠ c`, `b ≠ c`).
6. Show `g_perm * h_perm * g_perm⁻¹ * h_perm⁻¹ = h_perm` via algebraic identity:
   - `g_perm = swap a b * rest` (factor out the 2-cycle).
   - `rest` commutes with `h_perm` (supports disjoint: rest's support is in `g_perm.support \ {a, b}`, which is disjoint from `{a, b, c}` because `c` is free and `a, b` aren't in rest's support).
   - `g_perm * h_perm * g_perm⁻¹ = (swap a b) * h_perm * (swap a b)` (rest cancels).
   - `(swap a b) * h_perm * (swap a b) = h_perm⁻¹` (conjugation by a transposition inverts the 3-cycle starting with the same pair).
   - `h_perm⁻¹ * h_perm⁻¹ = h_perm` (because `h_perm` has order 3, so `h_perm⁻² = h_perm`).

**Sub-case B (no free point):** see `case4_commutator_witness` docstring. Needs a different construction (or recursive call after a commutator step that reduces support size).

## Already-proved infrastructure

- **`commutator_mem_normalClosure`** — generic Group: `g * h * g⁻¹ * h⁻¹ ∈ normalClosure({g})`. Used by all three cases.
- **Case 3 helpers** (`orderOf_g_eq_six_of_3_2_pattern`, etc.) — proved in PR #11. Reference patterns for cycleType / lcm / disjoint-decomposition arguments.

## Mathlib lemmas worth knowing

- `Equiv.Perm.cycleType_def` — `σ.cycleType = σ.cycleFactorsFinset.val.map (Finset.card ∘ support)`.
- `Equiv.Perm.mem_cycleFactorsFinset_iff` — `c ∈ g.cycleFactorsFinset ↔ c.IsCycle ∧ ∀ x ∈ c.support, g x = c x`.
- `Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub` — for removing a known factor.
- `Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset` — disjointness for `g * c⁻¹` against `c`.
- `Equiv.Perm.Disjoint.commute` — disjoint perms commute.
- `Equiv.Perm.card_support_eq_two : #f.support = 2 ↔ f.IsSwap` (in `GroupTheory.Perm.Support`).
- `Equiv.Perm.IsSwap` — `∃ x y, x ≠ y ∧ f = swap x y`.
- `Equiv.Perm.isThreeCycle_swap_mul_swap_same : a ≠ b → a ≠ c → b ≠ c → IsThreeCycle (swap a b * swap b c)`.
- `Equiv.Perm.IsThreeCycle.mem_alternatingGroup` — 3-cycles are even.
- `Equiv.swap_apply_def`, `Equiv.swap_apply_left`, `Equiv.swap_apply_right`, `Equiv.swap_swap` (involution), `Equiv.swap_inv`.

## Brute-force tactics

- `decide`, `native_decide` — for decidable goals over `Fin n` with concrete `n`.
- `aesop`, `omega`, `simp [...]`, `interval_cases`, `Finset.ext`.
- `group` — closes group-theoretic identities (e.g., associativity rearrangement).
- `Equiv.ext` then pointwise case analysis for permutation equality.

## Mathlib PR ambition (unchanged)

If all three leaves close, `alternatingGroup.isSimple_of_card_ne_four` becomes a real proof — the documented TODO at the top of `Mathlib/GroupTheory/SpecificGroups/Alternating.lean`.

---

*Updated post-Case-2-refactor. State: 3 leaf-witness sorries in Alternating.lean, all with verified-achievable signatures. The Case 2 retype was the result of hand-verifying the standard arguments and discovering the original simplification was wrong.*

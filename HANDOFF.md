# HANDOFF: closing the Galois leaf witnesses 🪜

Trevor's framing for whoever picks this up (human or AI):

> Lean into really fractal theorems — top down. Lots of sorries — ultimately, the sorries drop like flies. **Pretty at the top, ugly in the details (smooth-brained).**

After PRs #11 and #13, the Galois proof tree has been pushed down two fractal levels. The dispatcher is real proof; the case main theorems are real proof; only the **leaf witnesses** remain.

## State of the scaffold (2026-05-25, post-PR #13)

`FiniteSimpleGroups/Alternating.lean` has **3 sorries**, all of identical shape:

```lean
private theorem caseN_commutator_witness
    {n : ℕ} (g_perm : Equiv.Perm (Fin n))
    (h_caseN_hypothesis : ...) :
    ∃ h_perm : Equiv.Perm (Fin n),
      h_perm.IsThreeCycle ∧
      (g_perm * h_perm * g_perm⁻¹ * h_perm⁻¹).IsThreeCycle := by
  sorry
```

Each leaf says: **given a specific cycle structure on `g_perm`, produce a 3-cycle `h_perm` whose commutator with `g_perm` is also a 3-cycle.**

Once a leaf closes, the corresponding case main theorem is immediately a real proof (the wiring above the leaf is already in place: `commutator_mem_normalClosure` handles the membership claim, `push_cast` handles the alternatingGroup coercion).

## The principle (unchanged)

Don't try to write elegant leaf proofs. The structural decomposition at the top should be clean and obviously correct. The leaves can be brute force, `decide`, `aesop` spam, helper sub-lemmas with their own sorries — whatever works to make the bytes compile.

`sorry` is **structure**, not failure. Use it freely while shaping the proof tree.

**Lean in harder than a human might.** A human Lean prover often tries to find the "right" lemma. The smooth-brained approach is: don't. Build any chain that works. Refactor never.

## The three leaves

### `case1_commutator_witness` — long cycle

**Hypothesis:** `g_perm.cycleType` contains some `k ≥ 4`.

**Standard construction:** pick three consecutive points `a, b, c` of the long cycle (i.e., distinct, with `g_perm a = b ∧ g_perm b = c`). Take `h_perm := Equiv.swap a b * Equiv.swap b c` (this is the 3-cycle `(a b c)`).

**Sub-decomposition:**
1. **Extract `a, b, c`** — extract a cycle factor `c_long ∈ g_perm.cycleFactorsFinset` with `c_long.support.card ≥ 4`. Inside `c_long.support`, walk forward from any element to get three consecutive points.
2. **`h_perm.IsThreeCycle`** — mathlib has `Equiv.swap_mul_swap_isThreeCycle` (or similar; check `Equiv.Perm.Basic`).
3. **Commutator is a 3-cycle** — explicit computation. Either `Equiv.ext` with per-element case analysis, or use `Equiv.Perm.IsConj` + cycle-type machinery to show the commutator has cycleType `{3}`.

### `case2_commutator_witness` — multiple 3-cycles

**Hypothesis:** `g_perm.cycleType.count 3 ≥ 2`.

**Standard construction:** pick two distinct 3-cycle factors `c₁, c₂ ∈ g_perm.cycleFactorsFinset` with `cᵢ.support.card = 3`. From `c₁.support` extract `a, b, c`; from `c₂.support` extract `d, e, f`. Take `h_perm := (a b d)`.

**Sub-decomposition:**
1. **Extract `c₁, c₂`** — from `cycleType_def` + `count` arithmetic.
2. **Extract `a, b, d`** — from each cycle's support.
3. **`h_perm.IsThreeCycle`** — same as Case 1.
4. **Commutator is a 3-cycle** — explicit computation. The commutator turns out to be `(a c e)` or similar; verify via `Equiv.ext`.

### `case4_commutator_witness` — only 2-cycles

**Hypothesis:** every `m ∈ g_perm.cycleType` equals 2, `g_perm ≠ 1`, `n ≥ 5`.

**Split on free-point existence:**

**Sub-case A (free point):** if `g_perm.support.card < n`, there's a free point `e`. Pick a 2-cycle factor `c₀ ∈ g_perm.cycleFactorsFinset` with `c₀.support = {a, b}`. Take `h_perm := (a b e)`. The commutator works out to `(a b e)` itself (verify by `Equiv.ext`).

**Sub-case B (no free point):** then `n ≥ 8` and `g_perm` is e.g. `(a b)(c d)(e f)(g h)`. Pick two distinct 2-cycle factors, extract `(a b)` from one and `(c d)` from another. Take `h_perm := (a b c)`. The commutator works out to `(a c d)` (verify by `Equiv.ext`).

**Sub-decomposition:**
1. **`by_cases` on `g_perm.support.card < n`**.
2. **Extract a 2-cycle factor** — from `cycleType` containing 2.
3. **Extract a second 2-cycle factor (Sub-case B only)** — from `g_perm ≠ 1` + counting.
4. **`h_perm.IsThreeCycle`** — same as Case 1.
5. **Commutator is a 3-cycle** — explicit computation.

## Already-proved infrastructure

- **`commutator_mem_normalClosure`** — generic Group: `g * h * g⁻¹ * h⁻¹ ∈ normalClosure({g})`. Used by all three cases.
- **Case 3 helpers** (`orderOf_g_eq_six_of_3_2_pattern`, `orderOf_g_sq_eq_three_of_orderOf_six`, `cycleType_g_sq_replicate`, `card_cycleType_g_sq_eq_one`, `isThreeCycle_g_sq`) — proved in PR #11. Reference patterns for cycleType / lcm / disjoint-decomposition arguments.

## Mathlib lemmas worth knowing (refreshed)

For extracting cycle factors:
- `Equiv.Perm.cycleType_def` — `σ.cycleType = σ.cycleFactorsFinset.val.map (Finset.card ∘ support)`. Use with `Multiset.mem_map` to extract factors.
- `Equiv.Perm.mem_cycleFactorsFinset_iff` — `c ∈ g.cycleFactorsFinset ↔ c.IsCycle ∧ ∀ x ∈ c.support, g x = c x`.
- `Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub` — for removing a known factor.
- `Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset` — disjointness for `g * c⁻¹` against `c`.

For 3-cycles:
- `Equiv.Perm.IsThreeCycle` — `cycleType = {3}`.
- `Equiv.Perm.IsThreeCycle.mem_alternatingGroup` — 3-cycles are even.
- `Equiv.Perm.IsThreeCycle.swap_mul_swap` (or similar — check `GroupTheory.Perm.Basic`) — `(swap a b * swap b c).IsThreeCycle` for distinct `a, b, c`.

For commutator computations:
- `Equiv.ext` — pointwise equality of permutations.
- `Equiv.swap_apply_def`, `Equiv.swap_apply_left`, `Equiv.swap_apply_right`.
- `Equiv.Perm.isConj_iff_cycleType_eq` — if you've computed the commutator's cycleType, conjugation is automatic.

## Brute-force tactics worth trying liberally

- `decide`, `native_decide` — for decidable goals over `Fin n` with concrete `n`.
- `aesop` — general automation; surprisingly effective on Subgroup membership.
- `omega` — Nat / Int arithmetic, including some divisibility.
- `simp [...]` with a long list of `Equiv.swap_*`, cycle lemmas.
- `interval_cases` after bounding a Multiset count.
- `Finset.ext` then `decide` for support equalities on small `Fin n`.
- `group` — closes group-theoretic identities like `a * b * a⁻¹ * a = a * b`.

## The smooth-brained checkpoint

When tempted to clean up a leaf proof, ask: **does the case main theorem still type-check?** If yes, ship it. The leaf can be ugly. The reader of the scaffold sees the clean top; they don't care about the rubble underneath.

## Mathlib PR ambition (if you close all 3 leaves)

If all three leaves close, the entire Galois reduction (`exists_threeCycle_of_normal`) becomes a real proof, and so does `alternatingGroup_isSimple` for arbitrary `n ≥ 5`. The natural upstream PR is then:

```lean
theorem alternatingGroup.isSimple_of_card_ne_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (h : Fintype.card α ≠ 4) :
    IsSimpleGroup (alternatingGroup α)
```

This is the documented TODO at the top of `Mathlib/GroupTheory/SpecificGroups/Alternating.lean`. The mathlib reviewers know it's expected and supporting machinery is in place.

After landing upstream, `FiniteSimpleGroups/Alternating.lean` collapses to a one-line re-export.

Smooth-brain reward: the most architecturally beautiful possible outcome.

---

*Written 2026-05-25, post-PR #13. State of the scaffold: 3 leaf-witness sorries in Alternating.lean (all of identical shape) + 2 sorries in Adjacent/PrimeMul and SmallOrders. The Galois proof tree is real-proof from the dispatcher down to the leaves.*

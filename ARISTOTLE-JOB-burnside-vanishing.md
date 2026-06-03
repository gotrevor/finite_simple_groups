# Aristotle job: Burnside's vanishing lemma (analytic core)

**Status**: **SUBMITTED 2026-06-03** · **Project UUID `8451c8e2-8ef8-4dd8-a832-d2128920ceb6`**
(`aristotle-vanish`).  Awaiting result.

## Target (submitted, verified to elaborate in our v4.29.1 toolchain; only goal is `sorry`)

```lean
theorem burnside_vanishing_core {d : ℕ} (hd : 1 ≤ d) (ζ : Fin d → ℂ)
    (hζ : ∀ i, ∃ k : ℕ, 1 ≤ k ∧ ζ i ^ k = 1)
    (hint : IsIntegral ℤ ((∑ i, ζ i) / d)) :
    (∑ i, ζ i) = 0 ∨ ‖∑ i, ζ i‖ = d
```

This is Lemma A of Burnside's theorem: with `d = χ(1)`, `ζ i` the eigenvalues of `ρ g` (roots of
unity), `s = ∑ ζ i = χ(g)`.  Conclusion: `χ(g) = 0 ∨ |χ(g)| = χ(1)`.

## Proof strategy given to Aristotle
- `‖s‖ ≤ d` (triangle inequality, each `‖ζ i‖ = 1`), so `‖β‖ ≤ 1` for `β = s/d`.
- `β` lies in a number field; every embedding `φ` permutes roots of unity, so `‖φ(β)‖ ≤ 1`.
- **Kronecker** (mathlib `NumberField.Embeddings.pow_eq_one_of_norm_le_one`): `β = 0` or `β` is a
  root of unity (`‖β‖ = 1`).  `β = 0 ⇒ s = 0`; `‖β‖ = 1 ⇒ ‖s‖ = d`.

## When it returns
1. `aristotle list` (one-shot; NOT the live `show` TUI) → check `8451c8e2` status.
2. `aristotle download 8451c8e2-8ef8-4dd8-a832-d2128920ceb6 --destination /tmp/vanish.tar.gz`
   then `tar -xzf … -C /tmp/vanish && rg -n "sorry|burnside_vanishing_core" /tmp/vanish`.
3. **VERIFY in our kernel**: copy the proof into `CharacterTheory.lean`, `lake build`,
   `#print axioms burnside_vanishing_core` must be `[propext, Classical.choice, Quot.sound]` (no
   `sorryAx`, no new axioms).  Watch for v4.28 vs v4.29 API drift.
4. **IMMEDIATELY submit the next** bounded brick (see `PENDING_WORK.md` §A): candidates —
   eigenvalue structure (`χ(g)` is a sum of `χ(1)` roots of unity), or the central-character /
   class-sum integrality piece.

If `aristotle list` errors (no egress), skip and work locally.

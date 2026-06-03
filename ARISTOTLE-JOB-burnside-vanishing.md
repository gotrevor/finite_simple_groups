# Aristotle jobs: Burnside analytic lemmas

## Job 1 — Burnside vanishing lemma ✅ DONE + PORTED (2026-06-03)

**Project UUID `8451c8e2-8ef8-4dd8-a832-d2128920ceb6`** (`aristotle-vanish`).
**Returned, verified in our v4.29.1 kernel (`#print axioms`-clean), ported into
`CharacterTheory.lean` as `burnside_vanishing_core` (commit `c10fa8f`).**

Statement proved:
```lean
theorem burnside_vanishing_core {d : ℕ} (hd : 1 ≤ d) (ζ : Fin d → ℂ)
    (hζ : ∀ i, ∃ k : ℕ, 1 ≤ k ∧ ζ i ^ k = 1)
    (hint : IsIntegral ℤ ((∑ i, ζ i) / d)) :
    (∑ i, ζ i) = 0 ∨ ‖∑ i, ζ i‖ = d
```
Aristotle's proof used the number-field + Kronecker route (build `K = ℚ(ζ_i)`, `β = s/d ∈ K`
integral over `ℤ`, every embedding sends `β` to an average of roots of unity ⇒ norm ≤ 1, then
`NumberField.Embeddings.pow_eq_one_of_norm_le_one`).  No API drift v4.28 → v4.29.

## Job 2 — Scalar from maximal trace modulus (IN FLIGHT)

**Project UUID `e66a25d1-6646-4527-a08c-8e98ad175446`.**  Submitted 2026-06-03.
Project dir `/tmp/scalar_job` (ScalarJob.lean: target + the helper `eq_of_norm_sum_eq_card` as an
axiom — that helper is proven in-repo).

Target:
```lean
theorem matrix_scalar_of_pow_eq_one_of_norm_trace_eq {d n : ℕ} (hn : 1 ≤ n)
    (M : Matrix (Fin d) (Fin d) ℂ) (hM : M ^ n = 1) (hnorm : ‖Matrix.trace M‖ = (d : ℝ)) :
    ∃ ζ : ℂ, M = ζ • (1 : Matrix (Fin d) (Fin d) ℂ)
```
This is the **scalar step**: bridges `burnside_vanishing_core`'s output (`‖χ(g)‖ = χ(1)`) to
ingredient 6's input (`ρ g = c • 1`).  Strategy in the ScalarJob.lean docstring: charpoly roots are
`d` roots of unity, `‖∑‖ = d` ⇒ all equal `ζ` (via `eq_of_norm_sum_eq_card`), then `minpoly = X - ζ`
(squarefree since `M^n=1`) ⇒ `M = ζ • 1`.

### When it returns
1. `aristotle list` (one-shot) → check `e66a25d1` status (IDLE/DONE).
2. `aristotle download e66a25d1-6646-4527-a08c-8e98ad175446 --destination /tmp/scalar.tar.gz`,
   `tar -xzf … -C /tmp/scalar`, `grep -n "sorry" /tmp/scalar/.../ScalarJob.lean`.
3. **VERIFY** in our kernel: paste into a temp file (replace the `axiom eq_of_norm_sum_eq_card` with
   `import FiniteSimpleGroups.CharacterTheory` / `open FiniteSimpleGroups` so the real lemma is used),
   `lake env lean`, `#print axioms` must be `[propext, Classical.choice, Quot.sound]`.
4. Port into `CharacterTheory.lean`; then wrap to the Representation level
   (`‖ρ.character g‖ = finrank ⇒ ∃ c, ρ g = algebraMap ℂ (End ℂ V) c`) via
   `LinearMap.trace_eq_matrix_trace` + `LinearMap.toMatrix_pow`.
5. **Submit the next** brick — best candidate now: the `-1/p` endgame assembly piece, or (the deep one)
   the finite-set-of-irreducibles / column-orthogonality framework (ingredient 3, see PENDING_WORK §A
   and ON-LINE-REQUEST update 3).

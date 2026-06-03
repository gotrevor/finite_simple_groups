# Aristotle job: SL(2,F) is perfect (brick for the PSL(2,q) Iwasawa discharge)

## Why this brick

`PSLIwasawa.lean` reduces `PSL_isSimpleGroup` for `PSL 2 q` to five Iwasawa
obligations; one is **`commutator (PSL 2 q) = ⊤`** (perfect). Perfectness passes
to quotients, so it follows from **`SL(2,F)` perfect** for the relevant field.
mathlib v4.29.1 has the `PSL`/`SL` *definitions* but **no** SL(2) perfectness and
**no** PSL simplicity (checked 2026-06-03), so this is genuine new content, not
banned re-derivation (cf. the "one rule").

## Job 1 — `SL2_perfect` (IN FLIGHT)

**Project UUID `6f655ae9-4463-453c-bc08-61fac76ef29f`.** Submitted 2026-06-03.
Project dir `/tmp/sl2perfect` (`SL2Perfect.lean`: target + the cited axiom
`transvections_generate`, goal = `sorry`). Statement (elaborates clean in our
v4.29.1 kernel):

```lean
theorem SL2_perfect [Fintype F] (hF : 4 ≤ Fintype.card F) :
    commutator (SpecialLinearGroup (Fin 2) F) = ⊤
```

with `upper t = !![1,t;0,1]`, `lower t = !![1,0;t,1]`, and cited
`transvections_generate : Subgroup.closure (range upper ∪ range lower) = ⊤`
(standard: Gaussian elimination generates SLₙ over a field).

**Proof strategy** (in the file docstring): commutator subgroup contains every
transvection via `⁅diag(a,a⁻¹), upper s⁆ = upper ((a²−1)s)`; pick `a` with
`a²≠1` (exists for `|F|≥4`, since `X²−1` has ≤2 roots and `0` is excluded), so
`s ↦ (a²−1)s` is onto ⇒ every `upper t` (and `lower t`) is a commutator ⇒ by
`transvections_generate` the commutator subgroup is `⊤`.

### When it returns
1. `aristotle list` (one-shot) → check `6f655ae9` status.
2. `aristotle download 6f655ae9-4463-453c-bc08-61fac76ef29f --destination /tmp/sl2.tar.gz`,
   extract, `grep -n sorry` the returned file.
3. **VERIFY** in our v4.29.1 kernel (`lake env lean`), `#print axioms` must be
   `[propext, Classical.choice, Quot.sound, SL2PerfectJob.transvections_generate]`
   (only the one cited axiom).
4. Port into a new `FiniteSimpleGroups/SL2.lean` (or into `PSLIwasawa.lean`),
   then either discharge `transvections_generate` from mathlib's transvection
   API or keep it as a cited axiom; wrap perfectness up to `PSL 2 q` (quotient).
5. **Submit the next** brick — best candidates: another Iwasawa obligation made
   self-contained (the `IsKleinFour`/abelian Iwasawa subgroup, or `Nontrivial
   (PSL 2 q)` from `|SL₂(q)| = q(q²−1)`), or `transvections_generate` itself.

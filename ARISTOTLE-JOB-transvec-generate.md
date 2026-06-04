# Aristotle job: transvections generate SL(n,F) — the one open axiom of SLnPerfect

## Why this brick

`SLnPerfect.lean` proves `commutator_SLn_eq_top` (SL(n,F) perfect for `3 ≤ |n|`)
**modulo** one disclosed axiom `transvecSL_closure_eq_top`: the elementary
transvections generate `SL(n,F)`. Discharging it makes SL(n≥3) perfectness fully
axiom-clean — the first Iwasawa obligation for `PSL_isSimpleGroup_rank_ge_three`.

mathlib v4.29.1 has `Matrix.diagonal_transvection_induction` (every matrix is a
product of diagonals + transvections, needing only same-determinant diagonals) and
the Gaussian-reduction machinery, but NOT the SL-subgroup generation statement. The
crux is the Whitehead/Steinberg step: a determinant-1 diagonal is a product of
transvections.

## Job — `transvecSL_closure_eq_top` (IN FLIGHT)

**Project UUID `a4b84e9f-26f0-41d2-8208-2483d423ce9b`.** Submitted 2026-06-04.
Project dir `/tmp/slngen/SLnGen.lean`. Statement (elaborates clean in our v4.29.1
kernel — only the `sorry` warning):

```lean
def transvecSL {i j : n} (h : i ≠ j) (c : F) : SpecialLinearGroup n F :=
  ⟨transvection i j c, det_transvection_of_ne i j h c⟩

theorem transvecSL_closure_eq_top {n} [DecidableEq n] [Fintype n] {F} [Field F] :
    Subgroup.closure
      {g : SpecialLinearGroup n F | ∃ (i j : n) (h : i ≠ j) (c : F), g = transvecSL h c} = ⊤
```

This `transvecSL` is byte-identical to the one in `SLnPerfect.lean`, so a returned
proof ports directly onto the axiom (replace `axiom transvecSL_closure_eq_top` with
the theorem; `commutator_SLn_eq_top` then becomes axiom-clean).

⚠️ HARD target (Whitehead lemma); Aristotle may not fully close it. If it returns
partial/failed, decompose: submit the bounded sub-brick "a det-1 diagonal matrix is
a product of `transvection`s" first.

### When it returns
1. `aristotle list` → check `a4b84e9f` status.
2. `aristotle download a4b84e9f-26f0-41d2-8208-2483d423ce9b --destination /tmp/slngen-sol`.
3. **VERIFY** in v4.29.1 (`lake env lean`); `#print axioms` must be clean
   `[propext, Classical.choice, Quot.sound]` (pure mathlib).
4. Port onto `SLnPerfect.transvecSL_closure_eq_top` (drop the `axiom`, add the proof),
   confirm `commutator_SLn_eq_top` is now axiom-clean, commit. Then submit the next
   §E brick (the `SL(n,q) ↷ ℙ^{n-1}` action / 2-transitivity).

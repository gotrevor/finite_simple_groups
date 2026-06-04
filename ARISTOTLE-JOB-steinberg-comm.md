# Aristotle job: Steinberg commutator relation (brick for SL(n≥3) perfectness)

## Why this brick

The next tractable deep axiom after PSL(2,q) is `PSL_isSimpleGroup_rank_ge_three`
(LieType.lean). Its Iwasawa route needs `commutator (SL n F) = ⊤` for `n ≥ 3`.
Unlike `n = 2` (which needed `|F| ≥ 4` via the diagonal-conjugation trick), for
`n ≥ 3` **every** elementary transvection is a commutator of transvections via the
Steinberg/Chevalley type-`A` relation — no field-size restriction. mathlib v4.29.1
has `Matrix.transvection` + basic lemmas but NOT this commutator identity (checked
2026-06-04).

## Job — `steinberg_comm` (IN FLIGHT)

**Project UUID `4827df6e-ba1f-45f0-b1aa-cc243c1e7efa`.** Submitted 2026-06-04.
Project dir `/tmp/steinberg/Steinberg.lean`. Statement (elaborates clean in our
v4.29.1 kernel — only the `sorry` warning):

```lean
theorem steinberg_comm {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (a b : R) :
    transvection i k a * transvection k j b * transvection i k (-a) * transvection k j (-b)
      = transvection i j (a * b)
```

`transvection i j c = 1 + Matrix.single i j c`; `transvection i j c⁻¹ = transvection
i j (-c)` since `single i j` squares to 0 for `i ≠ j`. Hand-derived: expand
`x·y·x⁻¹·y⁻¹` using `single i k 1 * single k j 1 = single i j 1` and vanishing of all
squares + cross terms under `i≠j, i≠k, k≠j` ⇒ `1 + ab·single i j 1 = transvection i j (ab)`.

⚠️ Submit warned our toolchain (v4.29.1) ≠ Aristotle default (v4.28.0) and no
`.lake` shipped. Statement uses only stable mathlib primitives, so port should be
clean — but **VERIFY in our kernel** on return.

### When it returns
1. `aristotle list` (one-shot) → check `4827df6e` status (IDLE/SUCCESS).
2. `aristotle download 4827df6e-ba1f-45f0-b1aa-cc243c1e7efa --destination /tmp/steinberg-sol`,
   extract, find the proof.
3. **VERIFY** in v4.29.1 (`lake env lean`); `#print axioms` must be
   `[propext, Classical.choice, Quot.sound]` (NO custom axioms — it's pure mathlib).
4. Port into a new `FiniteSimpleGroups/SLnPerfect.lean` (or extend SL2.lean) as the
   first brick of SL(n≥3) perfectness; then IMMEDIATELY submit the next brick
   (candidate: "transvections t_{ij}(c), i≠j, generate SL(n,F)" — or its perfectness
   corollary for n≥3).

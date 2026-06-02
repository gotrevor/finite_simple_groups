# Online requests (open-web lookups the air-gapped box can't do)

The lean-yolo-box has no general internet (only Anthropic + Aristotle). Items below
need the open web — a textbook/paper proof, the state of an existing formalization,
or a literature check. Trevor runs a networked session to fulfill and commits the
findings back for a later lap. Newest first.

---

## 2026-06-02 — Bender base case: the central-product reduction of `C_G(F(G)) ≤ F(G)`

**Context / why this unblocks.** Bender's cornerstone `C_G(F*(G)) ≤ F*(G)`
(`genFittingSubgroup_self_centralizing`) is a proved theorem resting on ONE axiom,
`fittingSubgroup_eq_top_of_layer_eq_bot_of_le_center` (`GeneralizedFitting.lean`):

> finite `G`, `layer G = ⊥` (no components, `E(G)=1`), `F(G) ≤ Z(G)` ⟹ `F(G) = ⊤`.

This axiom is TRUE and sharp (the weaker "all minimal normals abelian" form is false —
`SL(2,𝔽₅)` counterexample, found by Aristotle). I have a machine-checked in-repo theorem
for the **solvable** case (`fittingSubgroup_eq_top_of_isSolvable_of_le_center`:
`[IsSolvable G] → F(G)≤Z(G) → F(G)=⊤`, ported from Aristotle, axiom-free). So the axiom
reduces to the gap:

> **`layer G = ⊥` ∧ `F(G) ≤ Z(G)` ⟹ `IsSolvable G`**
> (equivalently: a finite non-solvable group with central Fitting subgroup has a component).

Every elementary attempt to close this gap is circular: the natural induction on `|G|`
(quotient by a central minimal normal) stalls because `F(G/M) ≤ Z(G/M)` is **not**
inherited; and "non-solvable ∧ `F(G)≤Z(G)` ⟹ `E(G)≠1`" is itself equivalent to the base
case (provable from full Bender, but that's what we're proving). The genuine content is
the **central-product structure of `F*(G) = F(G)E(G)`** with `[F(G),E(G)] = 1` and
`C_G(F*(G)) = Z(F*(G))`.

**What I need from the literature.** The precise proof of Bender's cornerstone's base
case, broken into portable lemmas. Specifically:

1. **Aschbacher, *Finite Group Theory*, 31.12–31.13** — the full proof that
   `C_G(F*(G)) = Z(F*(G))`. Please transcribe the lemma chain (31.12 statement + proof,
   31.13 statement + proof), especially how it uses `C_G(E(G))`, the commuting
   `[E(G),F(G)]=1`, and the solvable Fitting fact `C_G(F(G)) ≤ F(G)` for solvable `G`.
2. **Kurzweil–Stellmacher, *The Theory of Finite Groups*, 6.5.8** (and the lemmas it
   cites, 6.5.1–6.5.7) — same theorem, often a cleaner write-up. Transcribe the proof
   and the exact prerequisite lemmas about `E(G)`/components it invokes.
3. **Which mathlib pieces exist?** Does mathlib (current, > v4.29.1) have: the generalized
   Fitting subgroup `F*`? the layer/components `E(G)`? `C_G(F(G)) ≤ F(G)` for solvable
   `G`? the central-product decomposition of `F*`? If any are formalized, give the exact
   declaration names so I can port/wire instead of rebuilding.
4. **Is there an existing Lean/Isabelle/Coq formalization** of Bender's cornerstone or of
   `F*(G)` self-centralizing? (e.g. in mathlib PRs, the Coq `BGsection*` Feit–Thompson
   files, GAP-adjacent projects.) Point me at it.

The deliverable that unblocks: the exact sequence of intermediate lemmas (statements
precise enough to formalize) that proves `layer G = ⊥ ∧ F(G) ≤ Z(G) → IsSolvable G`
(or directly `→ F(G) = ⊤`) from the solvable Fitting theorem + properties of the layer.

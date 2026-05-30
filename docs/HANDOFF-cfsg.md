# CFSG-track handoff 🤝

Resume point for the **Classification of Finite Simple Groups** scaffold
(top-down track). Companion to `docs/architecture.md` (the map) and the
FT-port `HANDOFF.md` (the frozen Feit–Thompson translation track).

Last updated: **2026-05-30** (after PR #51).

---

## Where we are

`main` @ `6ea18f2`. Build: green, `lake build` ~25s incremental, **0 sorries in
the trusted library**.

The CFSG statement lives in `FiniteSimpleGroups/Classification.lean`
(`IsClassified` five-way disjunction + `axiom CFSG`). As of PR #51 the scaffold
has three live workstreams:

| File | Status |
|---|---|
| `ProofStrategy.lean` | ✅ **deductive skeleton** — `classification_via_program` assembles the milestone axioms into a real proof of `IsClassified`. `#print axioms` = 7 named milestones + propext/Classical.choice/Quot.sound. |
| `FittingSubgroup.lean` | ⏳ `F(G)` defined; `normal_nilpotent_le_fittingSubgroup` + `center_le_fittingSubgroup` are **real (axiom-free)**; Fitting's Theorem is a cited axiom. |
| `PSLIwasawa.lean` | ⏳ `PSL2_isSimpleGroup_of_iwasawa` (sorry-free reduction to the Iwasawa criterion); the ℙ¹ action + 5 obligations are unbuilt. |

The FT-port (`FeitThompson/`) is **frozen at 11 cited axioms** — don't re-derive
Coq. Forward energy = CFSG top-down.

---

## Two next moves (pick one)

### A. Discharge Fitting's Theorem — `fittingSubgroup_isNilpotent` 🎯 (recommended)
This is the deepest-payoff real math; it unlocks `F*(G) = E(G)·F(G)`, the lens
the whole proof hangs on (Solomon p. 343).

- **The missing brick**: "the product (join) of two *normal* nilpotent subgroups
  of a finite group is nilpotent." mathlib has `Group.isNilpotent_prod` (external
  direct product) but **not** the internal-join version. Ref: Isaacs,
  *Finite Group Theory*, Thm 9.8; Kurzweil–Stellmacher §6.1.
- Then `F(G)` nilpotent follows (finite ⇒ the sSup is attained by a finite join).
- Bonus once `F(G)` is solid: define `E(G)` (layer / product of components) and
  `F*(G) = E(G)·F(G)`; state Bender's `F*`-theorem `C_G(F*(G)) ≤ F*(G)`.

### B. Build the PSL(2,q) ℙ¹ action for `PSLIwasawa.lean`
Flashier (turns the first opaque carrier into a real simplicity theorem) but
more plumbing. The reduction lemma already wires our carrier to mathlib's
`MulAction.IwasawaStructure.isSimpleGroup`; remaining obligations (roadmap table
in the file):

| Obligation | mathlib hooks |
|---|---|
| `MulAction (PSL 2 q) (ℙ¹ F_q)` (Möbius action) | `Projectivization`, GL action on lines |
| `Nontrivial (PSL 2 q)` | card of SL₂ / center |
| `commutator = ⊤` (perfect, q ≥ 4) | transvection generation |
| `IsQuasiPreprimitive` | PSL₂ 2-transitive ⇒ primitive |
| `IwasawaStructure` | `T(pt)` = unipotent stabilizer (abelian F_q⁺), conj-equivariant, `iSup = ⊤` |
| `FaithfulSMul` | projective action faithful |

Take `q` prime so `ZMod q` is the field (prime-power needs `GaloisField p k`).

---

## mathlib reconnaissance (master 2026-05-24)

- **Burnside `pᵃqᵇ`**: ❌ absent (only Burnside *transfer* + orbit *lemma*).
  Hard — needs char theory mathlib lacks. **Not** a quick axiom-discharge.
- **`Aₙ` simple (n ≥ 5)**: ✅ `alternatingGroup.isSimpleGroup`
  (`GroupTheory/SpecificGroups/Alternating/Simple.lean`, 2026-04-28). The
  `Alternating.lean` file's `TODO` comment is stale — the theorem exists.
- **Iwasawa criterion**: ✅ `MulAction.IwasawaStructure.isSimpleGroup`.
- **Group Fitting subgroup**: ❌ absent (every "Fitting" in mathlib is
  Lie-algebra / module decomposition).

---

## Conventions (standing)

- No mathlib upstream PRs from this repo. Bricks stay local.
- Merge over rebase; admin-merge on green CI.
- A local `axiom … -- per <source>` is only sound if it states the cited lemma
  *faithfully* (exact hypotheses). Sympy-spot-check any "we simplified the
  hypotheses" brick (lesson from the false `commutator_sup_le`, PR #49).
- Faithfulness gate: `#print axioms <decl>` should show only
  `propext / Classical.choice / Quot.sound` for anything claimed "real."

## Reference

- Solomon, *A Brief History of the CFSG*, Bull. AMS 38 (2001) — narrative.
- Aschbacher, *The Status of the CFSG*, Notices AMS 51:7 (2004).
- Local PDFs: `~/personal/data/cfsg/`.
- GLS Numbers 1–10 (AMS Surveys 40) — paywalled, NOT in Cornell alumni e-access.

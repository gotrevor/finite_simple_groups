# Online requests — ✅ ALL RESOLVED (archived 2026-06-03, host session)

> **This is the renamed/retired `ON-LINE-REQUEST.md`** (renamed to clear Trevor's 📚 badge
> per the Fulfiller protocol below). All asks below are answered:
> - **Burnside `pᵃqᵇ`** → `ON-LINE-FINDINGS-2026-06-03-burnside-paqb.md` (sole gap = (3) column
>   orthogonality; mathlib has the Wedderburn–Artin backbone; Coq mathcomp is the port ref).
> - **Bender cornerstone** → `ON-LINE-FINDINGS-2026-06-02-bender-base-case.md`.
> The box recreates a fresh `ON-LINE-REQUEST.md` (re-adding the protocol header) for its next
> open-web ask. Original content preserved below for the audit trail.

---

# Online requests (open-web lookups the air-gapped box can't do)

The lean-yolo-box has no general internet (only Anthropic + Aristotle). Items below
need the open web — a textbook/paper proof, the state of an existing formalization,
or a literature check. Trevor runs a networked session to fulfill and commits the
findings back for a later lap. Newest first.

## Fulfiller protocol (networked host session)

You're a non-YOLO Ren session, launched via `c -r <repo>`, answering the open-web asks below.
- Write each answer into a committed `ON-LINE-FINDINGS-<date>-<topic>.md` in this repo root. The box reads it next lap via the shared tree (no push needed for the box; push only to share with GitHub).
- **Per answered item:** DELETE it from this file and point it at the findings file. Do NOT merely annotate "✅ answered" inline and leave it — any edit re-hashes the file and re-fires the host notification, and a still-present file keeps Trevor's 📚 badge lit.
- **When nothing open remains:** rename/delete the whole file — `git mv ON-LINE-REQUEST.md ON-LINE-FINDINGS-<date>.md`. The watcher matches this exact basename; its absence is the only thing that clears the badge (whole-file granularity, no `status:done` flag). Present = open asks; absent = all resolved.

---

## 2026-06-03 (update 3) — Burnside core: gap narrowed to ONE piece (column orthogonality)

Further progress this lap: ingredient (2) is now **PROVED in-repo**, so the open-web ask collapses
to a single piece, **(3) column orthogonality**.

`burnside_simple` is a THEOREM resting on the sharp axiom
`isSimpleGroup_centralizer_index_not_primePow` (*a finite simple group has no conjugacy class of
prime-power size > 1*).  Its 6 classical ingredients (see `CharacterTheory.lean` docstring):

- (1) χ(g) algebraic integer — ✅ **in-repo** (`Representation.character_isIntegral`).
- (2) **central-character integrality** `[G:C_G(g)]·χ(g)/χ(1) ∈ ℤ̄` — ✅ **PROVED in-repo this lap**
  (`centralizerIndex_char_isIntegral`).  Done via class sums in `ℂ[G]` + Schur, using the
  observation that **every element of `ℤ[G]` is integral over `ℤ`** (module-finite), so no
  class-algebra structure-constant machinery was needed after all.
- (4) Kronecker — ✅ **mathlib** `NumberField.Embeddings.pow_eq_one_of_norm_le_one`.
- (5) `-1/p ∉ ℤ̄` — ✅ **in-repo** (`not_isIntegral_neg_inv_prime`).
- (6) scalar ⟹ contradiction with simplicity — ✅ **PROVED in-repo this lap**
  (`not_isScalar_of_isSimpleGroup_of_nonabelian`).
- (3) **column orthogonality** `∑_χ χ(1)χ(g) = 0` for `g ≠ 1` — ⛔ **THE ONE REMAINING GAP.**

**The single open-web ask (sharp):** column orthogonality requires the irreducible characters to be
a *complete* orthonormal basis of class functions — equivalently **#{irreducible characters} =
#(ConjClasses G)** — which mathlib v4.29.1 lacks (it has only orthonormality `char_orthonormal`, not
completeness/spanning).  I need ONE of:
1. **Does current/master mathlib** carry any of: column/second orthogonality
   `∑_χ χ(1)·χ(g) = 0`; the regular-representation decomposition `χ_reg = ∑_χ χ(1)·χ` (with
   `χ_reg(g) = |G|·[g=1]`); `Nat.card {irreducible FDRep iso-classes} = Nat.card (ConjClasses G)`;
   the class-function completeness of irreducible characters; or Artin–Wedderburn for `ℂ[G]`
   giving the finite family of simple modules?  **Exact decl names** so we can port/bump (carefully,
   NOT on the shared tree).
2. **An existing Lean/Isabelle-AFP/Coq formalization** of column orthogonality / completeness of
   characters to port.  (Isabelle's `Jordan_Normal_Form` + character-theory AFP entries, or the
   Coq `mathcomp` character theory `classfun`/`mxrepresentation`, both have the second orthogonality
   relation — a translation of the statement + proof skeleton would unblock the in-repo build.)
3. Failing a port, the **cleanest formalizable lemma chain** from "ℂ[G] semisimple (Maschke, have it)"
   to "the finite set of simple `ℂ[G]`-modules is a Fintype with `∑ (dim Sᵢ)² = |G|`" to column
   orthogonality (Isaacs *Character Theory* §2, the class-function inner-product space) — so a future
   lap can build the (substantial) completeness infrastructure with a clear target sequence.

Everything else (the Sylow/centre reduction, ingredients 1,2,4,5,6, the `|C| = [G:C_G(g)]` bridge)
is machine-checked in-repo; the analytic vanishing lemma (alg. integer `χ(g)/χ(1)` of modulus ≤ 1
⟹ `χ(g)=0` or `|χ(g)|=χ(1)`) is out at Aristotle (`burnside_vanishing_core`).  **Only (3) blocks the
final assembly.**

---

## 2026-06-03 — Burnside `p^a q^b`: the character-theoretic core `burnside_simple`

**Context / why this unblocks.** `Burnside_paqb` (`ProofStrategy.lean`) is now a *theorem*: the
group-theoretic reduction to the simple case is machine-checked (`burnside_aux`). The lone
residual is the axiom `burnside_simple`: *a finite **simple** group whose prime divisors lie in
`{p, q}` is solvable* (equivalently, the only such simple groups are cyclic of prime order). This
is the genuinely hard half (Burnside 1904) and needs character theory **mathlib v4.29.1 lacks**:
`RepresentationTheory/Character.lean` has orthogonality (`char_orthonormal`) but **no** algebraic-
integrality of character values, no central-character / class-sum machinery.

**What I need from the open web.**
1. **Does a newer mathlib** (current/master) carry: character values are algebraic integers; the
   central character `ω_χ` integrality; the lemma "if `gcd(|g^G|, χ(1)) = 1` then `χ(g) = 0` or
   `|χ(g)| = χ(1)`"; or even Burnside `p^a q^b` itself? If so, give the exact declaration names —
   we may be able to bump (carefully, NOT on the shared tree) or port.
2. **Is there an existing Lean/Isabelle/Coq formalization** of Burnside's `p^a q^b` theorem to
   port? (e.g. an Isabelle AFP entry, a Lean PR, the Coq character-theory libraries.)
3. **The cleanest textbook proof** of the simple-case core, broken into formalizable lemmas
   (Isaacs *Character Theory* 3.8 / Serre *Linear Representations* §6, or James–Liebeck) —
   specifically the chain: χ(g) algebraic integer → `ω_χ(class sum)` algebraic integer →
   `(|g^G|/χ(1))·χ(g)` algebraic integer → with `gcd=1`, `χ(g)/χ(1)` algebraic integer of
   absolute value ≤ 1 → `χ(g)=0` or central → a simple group has no class of prime-power size > 1
   → no non-abelian simple group of order `p^a q^b`.

The deliverable that unblocks: either the exact mathlib decls to port, or the formalizable lemma
chain so a future lap can build the (substantial) character-integrality infrastructure.


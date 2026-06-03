# Online requests (open-web lookups the air-gapped box can't do)

The lean-yolo-box has no general internet (only Anthropic + Aristotle). Items below
need the open web — a textbook/paper proof, the state of an existing formalization,
or a literature check. Trevor runs a networked session to fulfill and commits the
findings back for a later lap. Newest first.

---

## 2026-06-03 (update 2) — Burnside core SHARPENED; gap narrowed to 2 mathlib pieces

Significant progress this lap reduces what's actually needed from the open web:

1. **`burnside_simple` is now a THEOREM** (`FiniteSimpleGroups/Burnside.lean`), reduced by the
   machine-checked Sylow/centre argument to a single sharp axiom
   `isSimpleGroup_centralizer_index_not_primePow`: *a finite simple group has no conjugacy class
   of prime-power size `> 1`* (i.e. `(C_G(g)).index ≠ p^k` for `g ≠ 1`, `k ≥ 1`).  This IS
   Burnside's prime-power class-size lemma (Isaacs, *Character Theory*, Thm 3.8).
2. The classical proof of that lemma has **6 ingredients** (see `CharacterTheory.lean` docstring).
   Status after this lap:
   - (1) χ(g) is an algebraic integer — ✅ **PROVED in-repo** (`Representation.character_isIntegral`).
   - (4) Kronecker (alg. integer with all conjugates in unit disc ⟹ 0 or root of unity) — ✅
     **ALREADY in mathlib**: `NumberField.Embeddings.pow_eq_one_of_norm_le_one`.
   - (5) `-1/p ∉ ℤ̄` — ✅ **PROVED in-repo** (`not_isIntegral_neg_inv_prime`).
   - (2) **central-character integrality** `[G:C_G(g)]·χ(g)/χ(1) ∈ ℤ̄` — ⛔ STILL MISSING.
   - (3) **column orthogonality** `∑_χ χ(1)χ(g) = 0` for `g ≠ 1` — ⛔ STILL MISSING.
   - (6) scalar ⟹ proper normal subgroup — group/rep theory, buildable in-repo.

**The two things I still need from the open web (much narrower than before):**
- **(2) Central character / class-sum machinery.** Does current/master mathlib carry: the centre
  `Z(k[G])` of a group algebra; the class sums `z_C = ∑_{x∈C} x`; the fact that the `z_C` are
  integral over `ℤ` (non-negative integer structure constants); the central character
  `ω_χ : Z(ℂ[G]) → ℂ` with `ω_χ(z_C) = |C|χ(g)/χ(1)`?  Exact decl names if so.
- **(3) Column orthogonality / number of irreducibles = number of conjugacy classes.** mathlib has
  only row orthonormality (`char_orthonormal`).  Does master have the second orthogonality
  relation, or `Nat.card (irreducible characters) = Nat.card (ConjClasses G)`?  Decl names.
- **Either** of the above as an existing mathlib decl, **or** the cleanest formalizable lemma
  statements (Isaacs §2–3), unblocks the remaining build.  An existing Isabelle-AFP / Coq
  formalization of these two pieces to port would also do it.

*(Items 1–3 of the original 2026-06-03 request below are now partly answered in-repo; the
character-integrality half is done, so only the class-sum + column-orthogonality half remains.)*

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

---

## 2026-06-02 — Bender base case — ✅ IN-REPO PATH FOUND (this request is now LOW PRIORITY)

**Update (later same day):** the gap below was *cracked in-repo*, no open-web input needed.
Key realization: under `F(G) ≤ Z(G)`, the quotient `G/Z(G)` has `F(G/Z(G)) = ⊥` (not merely
central), which makes the solvability induction go through. The whole solvability statement is
now a machine-checked theorem (`isSolvable_aux`, `GeneralizedFitting.lean`), resting on a single
sharp axiom `layer_quotient_center_eq_bot` (a central quotient of a component-free group is
component-free). Grün's lemma — the crux of that axiom — is also proved in-repo
(`center_quotient_center_eq_bot_of_perfect`, `PerfectCentralExtension.lean`). Only a mechanical
final assembly (the quasisimple-central-extension lemma + component pullback) remains, with all
prerequisites built. **The literature transcription below is no longer load-bearing**, though a
cross-check of any existing Lean/Isabelle/Coq formalization of `F*(G)`/Bender (item 4) would still
be a nice-to-have. Items 1–3 can be skipped.

---

### (Original, now superseded) Bender base case: the central-product reduction of `C_G(F(G)) ≤ F(G)`

> ✅ **ANSWERED 2026-06-02 (host)** → `ON-LINE-FINDINGS-2026-06-02-bender-base-case.md`.
> Still-useful bits despite supersession: **(item 4)** verified that **no
> Lean/Isabelle/Coq formalization of `F*(G)`/Bender exists anywhere** — base
> `math-comp` has only ordinary `'F(G)`; `math-comp/odd-order` has only the
> *solvable* `C_G(F(G))⊆F(G)` (`cent_sub_Fitting`, B&G 1.3 / P. Hall); this repo is
> first. **(remaining assembly)** the quasisimple-central-extension lemma + the
> component pullback are exactly **K-S 6.5.1**, transcribed verbatim with a 5-step
> portable lemma list in the findings (feed it to Aristotle job `9f7b6b74`). Plus
> **(item 3)** mathlib has no Fitting subgroup at all, but its new `IsSubnormal`
> (Capdeboscq+Testa 2026) is worth aligning the repo's against for upstreaming.

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

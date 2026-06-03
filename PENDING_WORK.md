# Pending work — open axioms & attack paths

Per the unblock protocol: a live inventory of every open `axiom` in the repo, with concrete
attack paths.  Updated 2026-06-03.

## A. Genuinely attackable now (active thread)

### `isSimpleGroup_centralizer_index_not_primePow` (`Burnside.lean`)
*Burnside's prime-power class-size lemma: a finite simple group has no conjugacy class of
prime-power size `> 1`.*  Sole residual axiom of `burnside_simple` after the Sylow/centre
reduction.  Six classical ingredients; **1, 2, 4, 5, 6 are DONE** (in-repo or mathlib).  The sole
remaining gap is **ingredient 3 (column orthogonality)**, plus the analytic vanishing lemma (out at
Aristotle) and the final assembly.

Done this far (all in `CharacterTheory.lean`, `#print axioms`-clean):
- (1) `Representation.character_isIntegral` — χ(g) algebraic integer.
- (2) `centralizerIndex_char_isIntegral` — `[G:C_G(g)]·χ(g)/χ(1) ∈ ℤ̄`.  Built via class sums in
  `ℂ[G]` + Schur, using that **`ℤ[G]` is module-finite over `ℤ`** (every element integral over `ℤ`)
  — the textbook structure-constant argument was unnecessary.  Supporting: `classSum`,
  `classSum_isIntegral`, `classSum_central`, `trace_asAlgebraHom_classSum`,
  `exists_scalar_isIntegral_of_central`, and the `filter_isConj_card_eq_index` bridge
  (class size = centralizer index).
- (4) Kronecker — mathlib `NumberField.Embeddings.pow_eq_one_of_norm_le_one`.
- (5) `not_isIntegral_neg_inv_prime` — `-1/p ∉ ℤ̄`.
- (6) `not_isScalar_of_isSimpleGroup_of_nonabelian` — a nontrivial scalar element in a faithful rep
  of a nonabelian simple group is impossible.  Plus `Representation.norm_character_le` (`‖χ(g)‖ ≤ χ(1)`).

**Ingredient 3 — column orthogonality `∑_χ χ(1)χ(g) = 0` (g ≠ 1).**  THE remaining gap; needs the
irreducible characters to form a *complete* class-function basis (= `#irreducibles = #ConjClasses`),
which mathlib lacks (only orthonormality `char_orthonormal`).  Three attack paths:
1. **Port from elsewhere** (cheapest if it exists).  Check master mathlib / Isabelle-AFP / Coq
   mathcomp for column orthogonality or completeness of characters.  See `ON-LINE-REQUEST.md`
   (2026-06-03 update 3) for the exact ask.
2. **Regular-representation route (in-repo).**  Build `χ_reg(g) = |G|·[g=1]` (character of
   `leftRegular ℂ G = ofMulAction ℂ G G`; trace of a permutation rep = fixed-point count — concrete,
   reusable, farmable), then the decomposition `χ_reg = ∑_χ χ(1)·χ` over the finite family of
   irreducibles ⇒ column orthogonality.  The hard sub-piece is the *finite family of irreducibles*
   with multiplicity = dimension (needs Artin–Wedderburn / semisimple-module enumeration; mathlib
   has Maschke `IsSemisimpleRing ℂ[G]` but not the Fintype of simple factors).
3. **Class-function inner-product space (in-repo).**  Class functions form a `ℂ`-vector space of
   dim `#ConjClasses`; irreducible characters are orthonormal (`char_orthonormal`) hence linearly
   independent; show they *span* (= count them) ⇒ basis ⇒ second orthogonality.  Same hard sub-piece
   (`#irreducibles = #ConjClasses`).

After ingredient 3: assemble the sharp axiom from
`-1/p = ∑_{χ≠1}(χ(1)/p)χ(g)` (column orthogonality at `1` vs `g`) + `not_isIntegral_neg_inv_prime`
⇒ ∃ nontrivial χ, `p∤χ(1)`, `χ(g)≠0` ⇒ (vanishing lemma) `g` scalar in χ ⇒
`not_isScalar_of_isSimpleGroup_of_nonabelian` ⇒ `False`.  The vanishing lemma
(`burnside_vanishing_core`) is OUT at Aristotle (`8451c8e2`); port + verify when it returns.

## B. Deep / intended-permanent (do NOT spend a lap trying to "crack")

- **CFSG milestones** (`ProofTree.lean`, `ProofStrategy.lean`): `B_theorem`, `trichotomy_theorem`,
  `aschbacher_dichotomy`, `Feit_Thompson_odd_order`, `componentType_standardForm`,
  `standardForm_isClassified`, `standardType_hasBNPair`, `bnPair_isClassified`,
  `oddType_isClassified`, `evenType_dichotomy`, `componentType_isClassified`,
  `quasithin_isClassified`, `nonQuasithin_char2_isClassified`.  Each is a decades-long theorem;
  the repo only machine-checks how they *compose* into `IsClassified`.  Attack = port a Coq/Isabelle
  proof (Feit–Thompson exists in Coq) — multi-year, out of scope for a lap.
- **Family simplicity**: `alternatingGroup_isSimple` (`Alternating.lean` — bucket C, delete when the
  mathlib pin passes PR #36524; do NOT re-derive on the shared tree), `PSL/PSU/PSp/POmega`
  (`LieType.lean`), the 10 exceptionals (`Exceptional.lean`), `Co1/Co2/Co3` (`Sporadics.lean`).
  Deep; intended.

## C. Soundness-audit TODO (cheap, valuable — flagged 2026-06-03)

The Bender axiom once slipped in **false**.  Re-read each `axiom`'s *statement* for faithfulness:
the `IsFSG`-typeclass milestone axioms have complex conclusions worth a careful read.  The newly
added `isSimpleGroup_centralizer_index_not_primePow` was audited this lap (true: it is exactly
Burnside's lemma; abelian-simple = prime-cyclic gives index 1 = `p^0`, excluded by `k ≥ 1`).

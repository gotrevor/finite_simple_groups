# Pending work — open axioms & attack paths

Per the unblock protocol: a live inventory of every open `axiom` in the repo, with concrete
attack paths.  Updated 2026-06-03.

## A. Genuinely attackable now (active thread)

### `isSimpleGroup_centralizer_index_not_primePow` (`Burnside.lean`)
*Burnside's prime-power class-size lemma: a finite simple group has no conjugacy class of
prime-power size `> 1`.*  This is the sole residual axiom of `burnside_simple` after this lap's
machine-checked Sylow/centre reduction.  Six classical ingredients; 1, 4, 5 are DONE (in-repo or
mathlib), so the residual is ingredients **2 + 3 + 6**.

Three attack paths:
1. **Build the class-sum / central-character machinery in-repo** (ingredient 2).  Define
   `Z(ℂ[G])` and the class sums `z_C ∈ MonoidAlgebra ℂ G`; prove they are integral over `ℤ`
   (the `ℤ`-subalgebra they generate is finite over `ℤ` because `z_C z_D = ∑ a_{CDE} z_E` with
   `a ∈ ℤ_{≥0}`); define `ω_χ` via Schur (`ρ(z_C)` is a scalar for irreducible `ρ`) and read off
   `ω_χ(z_C) = |C|χ(g)/χ(1)`.  → `[G:C_G(g)]·χ(g)/χ(1)` integral.  (Aristotle-farmable in pieces.)
2. **Build column orthogonality in-repo** (ingredient 3).  mathlib has row orthonormality
   (`char_orthonormal`) and the irreducible decomposition (`FDRep`, Maschke).  Derive
   `#{irreducibles} = #(ConjClasses G)` (class functions basis), then the second orthogonality
   relation `∑_χ χ(1)χ(g) = 0` for `g ≠ 1`.  Then assemble: `-1/p = ∑_{χ≠1}(χ(1)/p)χ(g)`; if all
   nonzero terms had `p | χ(1)` the RHS would be integral (ingredient 1), contradicting
   `not_isIntegral_neg_inv_prime` — so some `χ` has `p ∤ χ(1)`, `χ(g) ≠ 0`, hence (Lemma A,
   `burnside_vanishing_core`) `g` acts as a scalar in `χ`.
3. **Ingredient 6 (in-repo, independent of 2/3):** the set `{h : ρ_χ(h) is a scalar}` is a normal
   subgroup `N`; for a faithful nontrivial irreducible `χ` of a simple group, `N` proper (else `χ`
   abelian image) and nontrivial (contains the scalar `g`) — contradiction with simplicity.  This
   is pure group/rep theory and can be formalized now to de-risk the assembly.

Supporting bricks already in `CharacterTheory.lean`: `trace_isIntegral_of_pow_eq_one`,
`Representation.character_isIntegral`, `not_isIntegral_neg_inv_prime`.  Lemma A
(`burnside_vanishing_core`) is OUT at Aristotle (`8451c8e2`); when it returns, port + verify.

Next concrete sub-brick to build/farm: **eigenvalue structure** — `χ(g)` is a sum of exactly
`χ(1)` roots of unity (the eigenvalues of `ρ g`), needed to bound `‖χ(g)‖ ≤ χ(1)` and to feed
`burnside_vanishing_core`.  (Have: trace = sum of charpoly roots, roots are roots of unity.
Missing: the multiset has card `= finrank` and elements are roots of unity, packaged for the ζ
form.)

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

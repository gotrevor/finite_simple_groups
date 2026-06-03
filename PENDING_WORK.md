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

Also DONE (analytic side, this lap):
- **Vanishing lemma** `burnside_vanishing_core` — `∑ ζ_i = 0 ∨ ‖∑ ζ_i‖ = d` for `d` roots of unity
  with `(∑ζ_i)/d` integral.  Discharged by Aristotle (`8451c8e2`), verified, ported (`c10fa8f`).
- **Equality case** `eq_of_norm_sum_eq_card` — `d` unit-modulus numbers summing to modulus `d` are
  all equal (the analytic half of "`‖χ(g)‖ = χ(1)` ⇒ `ρ g` scalar").
- **Regular character** `character_leftRegular_eq` (`χ_reg(g) = |G|·[g=1]`) and
  `sum_character_leftRegular_mul` (`∑_g χ_reg(g)·f(g) = |G|·f(1)`) — Route-B bricks for (3).

**Ingredient 3 — column orthogonality `∑_χ χ(1)χ(g) = 0` (g ≠ 1).**  THE remaining gap.  Answered
by the host: see `ON-LINE-FINDINGS-2026-06-03-burnside-paqb.md`.  Key facts from there:
- mathlib has **no** column orthogonality (v4.29.1 = master), BUT it **has the Wedderburn–Artin
  backbone**: `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
  (`RingTheory/SimpleModule/IsAlgClosed.lean`) gives `ℂ[G] ≃ₐ[ℂ] ∏ᵢ Matrix (Fin dᵢ) (Fin dᵢ) ℂ`
  (with `ℂ[G]` semisimple via Maschke).  So the finite family of irreducibles + `∑dᵢ²=|G|` is
  derivable, not from-scratch.
- **Coq mathcomp `integral_char.v`** fully formalizes Burnside `pᵃqᵇ` (Isaacs Ch.2–3) — the
  decl-for-decl port blueprint; `second_orthogonality_relation` + `NirrE` (`#Irr=#classes`) are the
  relevant decls.  No Lean/Isabelle equivalent — this repo would be the first in Lean.

**Recommended: Route B (regular character).**  Build only `χ_reg = ∑_{χ∈Irr} χ(1)·χ` (sub-lemma 2;
sub-lemma 1 `χ_reg(g)=|G|·[g=1]` and the inner-product `sum_character_leftRegular_mul` are DONE).
Remaining work: (a) the **finite family `Irr(G)`** of irreducibles (index a complete duplicate-free
set — the one shared sticking point; use the Wedderburn `∏Mᵢ` factors as the index), and (b) the
semisimple decomposition "character of a rep = `∑ (multiplicity)·(irreducible char)`" with
multiplicity `= ⟨χ_reg,χ⟩ = χ(1)` (have `char_orthonormal` for the inner product).
Route A (full second orthogonality) is also now tractable; its one gap is "`{classSum C}` is a basis
of `Z(ℂ[G])`" (have `classSum`, `classSum_central`).

After ingredient 3: assemble the sharp axiom from
`0 = χ_reg(g) = ∑_χ χ(1)χ(g) = 1 + p·θ` with `θ ∈ ℤ̄` ⇒ `θ = -1/p ∈ ℤ̄`, contradicting
`not_isIntegral_neg_inv_prime`.  (For each nontrivial χ: if `p∤χ(1)` then `χ(g)/χ(1) ∈ ℤ̄`
(ingredient 2 + gcd) of modulus ≤ 1 ⇒ (vanishing lemma) `χ(g)=0` or `g` scalar ⇒
`not_isScalar_of_isSimpleGroup_of_nonabelian`; so the `p∤χ(1)` terms vanish.)  The scalar step
`‖χ(g)‖=χ(1) ⇒ ρ g scalar` is OUT at Aristotle (`e66a25d1`, matrix form); port + wrap to the
Representation level when it returns.

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

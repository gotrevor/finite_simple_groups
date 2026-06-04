# Pending work — open axioms & attack paths

Per the unblock protocol: a live inventory of every open `axiom` in the repo, with concrete
attack paths.  Updated 2026-06-03.

## ✅ A. Burnside `pᵃqᵇ` — COMPLETE (fully machine-checked, no custom axioms)

`Burnside.isSimpleGroup_centralizer_index_not_primePow` is now a **theorem**
(`CharacterTheory.burnside_class_size`).  `Burnside.burnside_simple` and `ProofStrategy.Burnside_paqb`
`#print axioms` = `[propext, Classical.choice, Quot.sound]` — **no custom axioms**.  All three former
gaps discharged this lap (2026-06-03):
- **Gap 1** (irreducibility of each Wedderburn factor `Rᵢ`): `isIrreducible_of_surjective_algHom`
  (transfer simplicity from the natural matrix module along the surjective `Ψᵢ = πᵢ∘e` via
  `LinearMap.isSimpleModule_iff_of_bijective`).  No Aristotle needed.
- **Gap 2** (scalar bridge `‖trace(ρg)‖ = d ⇒ ρg scalar`): `matrix_scalar_of_pow_eq_one_of_norm_trace_eq`
  (ported from Aristotle `e66a25d1`, re-verified) + `matrix_trace_zero_or_scalar`.
- **Gap 3** (trivial factor unique, `T = 1`): existence `exists_trivial_factor` (augmentation/idempotent,
  ported from Aristotle `a3e3d823`) + uniqueness `trivial_factor_unique` (**proved locally** — the
  averaging-idempotent `w = |G|⁻¹∑g` has nonnegative-integer component traces summing to 1, so two
  trivial factors would force the sum ≥ 2; `matrix_idempotent_trace_natCast` via `IsProj.trace`).

Nothing left to do on the Burnside thread.  (Historical detail below retained for the record.)

<details><summary>Historical: the former axiom and its 6 ingredients</summary>

### `isSimpleGroup_centralizer_index_not_primePow` (`Burnside.lean`) — now discharged
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

**Ingredient 3 — column orthogonality `∑_χ χ(1)χ(g) = 0` (g ≠ 1).**  KEYSTONE NOW BUILT (Route B,
2026-06-03).  `exists_wedderburn_character_decomp` (axiom-clean) gives
`χ_reg(g) = ∑ᵢ dᵢ·trace(Rᵢ g)` via Artin–Wedderburn `ℂ[G] ≃ₐ ∏ᵢ Mₐᵢ(ℂ)`, where
`Rᵢ : G →* Mₐᵢ(ℂ)` is the `i`-th projection of `single g 1`; with `character_leftRegular_eq`
(`χ_reg(g)=|G|[g=1]`) this is exactly `∑ᵢ dᵢ·χᵢ(g) = 0` for `g ≠ 1`.  Supporting (all green,
axiom-clean): `trace_mulLeft_pi_matrix` (Aristotle `eed8a149`, ported+verified), `conj_mulLeft`,
`character_ofMulAction_eq_trace_mulLeft`, `repOfMatrixHom` + `repOfMatrixHom_character`
(Rᵢ as a `Representation`, character = trace), `trace_matrixHom_isIntegral` (trace ∈ ℤ̄),
`norm_trace_matrixHom_le` (‖trace‖ ≤ dᵢ), `isIntegral_of_coprime_smul` (Bézout: `m·β,n·β ∈ ℤ̄`,
`gcd(m,n)=1 ⇒ β ∈ ℤ̄`), `injective_of_isSimpleGroup_of_exists_ne` (faithfulness of nontrivial Rᵢ).

**THREE residual gaps to finish the axiom** (each a clean named target):
1. **Irreducibility of each `Rᵢ`** (needed for ingredient 2 / Schur on the factor).  Reduces to
   (a) *natural matrix module is simple*, `IsSimpleModule (Matrix (Fin d) (Fin d) ℂ) (Fin d → ℂ)`
   — OUT at Aristotle job `dc41262f` (`simplejob`); plus (b) transfer along the surjection
   `Rᵢ.asAlgebraHom : ℂ[G] ↠ Mₐᵢ ≅ End ℂ (Fin dᵢ→ℂ)` (image = full End ⇒ only ⊥/⊤ invariant).
   mathlib has the *algebra*-map transfer (`isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective`,
   needs comm base — n/a here) but NOT a ring-hom-surjective transfer; build "asAlgebraHom surjective
   ⇒ IsIrreducible" directly from (a).  ALT: surjectivity of `Rᵢ.asAlgebraHom` is itself a sub-task
   (`πᵢ ∘ e` surjective onto the factor).
2. **Scalar bridge** `‖χ(g)‖ = χ(1) ⇒ ρ g = c•1` — OUT at Aristotle `e66a25d1` (`scalar_job`,
   matrix form `matrix_scalar_of_pow_eq_one_of_norm_trace_eq`); when it returns, port + wrap to the
   Representation level, then combine with `burnside_vanishing_core` + Kronecker to get
   `χᵢ(g)=0 ∨ g scalar`, and `not_isScalar_of_isSimpleGroup_of_nonabelian` (have, needs only
   faithfulness) kills the scalar case ⇒ `χᵢ(g)=0` for nontrivial p∤dᵢ factors.
3. **Trivial multiplicity `T = 1`** — exactly one factor is the trivial rep, giving the `+1` in
   `0 = T + p·θ`.  CLEANEST PATH (avoids the iso-class bijection): for a *nonabelian simple* G,
   `[G,G] = G` (commutator is normal, nontrivial ⇒ =G), so `G^ab = 1`, so the only linear character
   is trivial ⇒ exactly one `dᵢ = 1` factor, which is the trivial.  Still needs "number of `dᵢ=1`
   factors = #linear chars = |G^ab|" — research the cleanest mathlib route (see ON-LINE-REQUEST).
   ALT: row orthogonality `char_orthonormal` gives `⟨χ_reg, χ_triv⟩ = 1` but needs the
   multiplicity-decomposition theory mathlib lacks.

**Final assembly** (once 1–3 land): obtain the family once; `hdec g` gives `∑ᵢ dᵢ·trace(Rᵢ g) = 0`.
Split off the unique trivial factor (`+1`), nontrivial p∤dᵢ vanish (gap 2), p|dᵢ give `p·(dᵢ/p)·χᵢ(g)`
with `(dᵢ/p)·χᵢ(g) ∈ ℤ̄` (gap-1 irreducibility ⇒ ingredient 2 + gap-2 vanishing-or-bound + Bézout) ⇒
`0 = 1 + p·θ`, `θ ∈ ℤ̄`, so `θ = -1/p` contradicts `not_isIntegral_neg_inv_prime`.

Older notes (Route A/B background, still valid):
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

</details>

## B. Deep / intended-permanent (do NOT spend a lap trying to "crack")

- **CFSG milestones** (`ProofTree.lean`, `ProofStrategy.lean`): `B_theorem`, `trichotomy_theorem`,
  `aschbacher_dichotomy`, `Feit_Thompson_odd_order`, `componentType_standardForm`,
  `standardForm_isClassified`, `standardType_hasBNPair`, `bnPair_isClassified`,
  `oddType_isClassified`, `evenType_dichotomy`, `componentType_isClassified`,
  `quasithin_isClassified`, `nonQuasithin_char2_isClassified`.  Each is a decades-long theorem;
  the repo only machine-checks how they *compose* into `IsClassified`.  Attack = port a Coq/Isabelle
  proof (Feit–Thompson exists in Coq) — multi-year, out of scope for a lap.
- **Family simplicity**: `alternatingGroup_isSimple` (`Alternating.lean` — bucket C, delete when the
  mathlib pin passes PR #36524; do NOT re-derive on the shared tree), `PSU/PSp/POmega` and the
  `PSL n q` axiom for `n ≥ 3` (`LieType.lean`), the 10 exceptionals (`Exceptional.lean`),
  `Co1/Co2/Co3` (`Sporadics.lean`).  Deep; intended.  **NB:** `PSL_isSimpleGroup` *for `n = 2`* is
  NOT in this bucket — it is the ACTIVE tractable thread, see §D.

## D. ✅ COMPLETE — `PSL(2,q)` simplicity via Iwasawa (DONE 2026-06-04)

**`PSL2_isSimpleGroup (q) [Fact prime q] (hq : 4 ≤ q) : IsSimpleGroup (PSL 2 q)`
is PROVEN and `#print axioms`-clean** (`[propext, Classical.choice, Quot.sound]`).
This **discharges the deep CFSG `axiom PSL_isSimpleGroup` at `n = 2`** — the one
tractable family case.  All six Iwasawa obligations are machine-checked in
`FiniteSimpleGroups/SL2.lean`; the assembly is `PSL2_isSimpleGroup` via
`PSL2_isSimpleGroup_of_iwasawa` (`PSLIwasawa.lean`).  mathlib v4.29.1 has the
`PSL`/`SL` defs + transvection machinery but NO SL(2)/PSL simplicity, so this is
genuine new content (consistent with the "one rule").

**§D-followup — DONE 2026-06-04 (axiom wired + soundness fix).** The former
monolithic `axiom PSL_isSimpleGroup (n q) (2≤n) (¬(n=2∧q≤3))` was **unsound** for
composite `q` (`ZMod 6` not a field ⇒ `PSL(2,ZMod 6)` not simple). Replaced by:
- `axiom PSL_isSimpleGroup_rank_ge_three (n q) [Fact prime q] (3 ≤ n)` in
  `LieType.lean` — the genuinely-deep, now prime-scoped (hence true) higher-rank case;
- `theorem PSL_isSimpleGroup (n q) [Fact prime q] (2≤n) (¬(n=2∧q≤3))` in `SL2.lean`
  — dispatches `n=2` → `PSL2_isSimpleGroup` (machine-checked), `n≥3` → the axiom.
`#print axioms PSL_isSimpleGroup` = `[propext, Classical.choice,
PSL_isSimpleGroup_rank_ge_three, Quot.sound]` — n=2 contributes no debt.

Progress (all in `FiniteSimpleGroups/SL2.lean`, `#print
axioms`-clean — `[propext, Classical.choice, Quot.sound]`):

- ✅ **perfect** `commutator (PSL 2 q) = ⊤` — `PSL2_perfect` (q prime ≥ 4), from
  `SL2_perfect` (transvections generate SL(2,F); each is a commutator via
  `⁅diag(a,a⁻¹), upper s⁆ = upper((a²-1)s)`) descended to the quotient.
- ✅ **nontrivial** `Nontrivial (PSL 2 q)` — `PSL2_nontrivial` (all primes q;
  SL(2,q) non-abelian ⇒ quotient by center nontrivial).
- ✅ **faithfulness groundwork** — `center_SL2`: `center (SL(2,F)) = {±1}`, the
  kernel of `SL ↠ PSL`.

3. ✅ **`MulAction (PSL 2 q) ℙ¹`** — `SL2.psl1Action` (DONE 2026-06-03).  Built the
   SL(2,F) action on `Fin 2 → F` (mulVec; `DistribMulAction` + `SMulCommClass`),
   got `MulAction (SL 2 F) (ℙ¹)` from mathlib's instance, then DESCENDED to PSL via
   `QuotientGroup.lift (toPermHom) (center_le_ker)` + `MulAction.compHom`
   (`center_smul_eq`: scalars fix every line).

- ✅ **faithful** `FaithfulSMul (PSL 2 q) ℙ¹` — `SL2.pslFaithful` (DONE 2026-06-03).
  Proved `ker (toPermHom (SL 2 q) ℙ¹) ≤ center` (`ker_le_center`, the reverse of
  `center_le_ker`; combined ⇒ `ker = center`). The math core `mem_center_of_smul_eq`
  ("g fixes every line ⇒ g scalar") went **fully elementary** rather than via
  `exists_eq_smul_id`: testing the three lines `[e₁],[e₂],[e₁+e₂]` forces
  `g 1 0 = g 0 1 = 0` and `g 0 0 = g 1 1` (`parallel_of_fixes`), then `det=1` ⇒
  `g 0 0 ² = 1` ⇒ `g = ±1 ∈ center` (`center_SL2`). Plumbing: `pslPermHom` =
  `QuotientGroup.lift (center) (toPermHom) (center_le_ker)`; injective via
  `injective_iff_map_eq_one` + `QuotientGroup.eq_one_iff`; `pslFaithful` then from
  `eq_of_smul_eq_smul` since `g•x = pslPermHom g x` (compHom) and `Sym` is faithful.

- ✅ **quasi-preprimitive** `IsQuasiPreprimitive (PSL 2 q) ℙ¹` — `SL2.pslQuasiPreprimitive`
  (DONE 2026-06-03).  Proved PSL(2,q) **2-transitive** on ℙ¹ (`psl_two_trans` on
  points, `psl_two_pretrans` on `Fin 2 ↪ ℙ¹`), then `isPreprimitive_of_is_two_pretransitive`
  ⇒ `IsPreprimitive` ⇒ (instance `IsPreprimitive.isQuasiPreprimitive`) quasi-preprimitive.
  Geometric core `exists_sl2_maps_ref`: distinct lines `[v]≠[w]` ⇒ `d=det[v|w]≠0`
  (`parallel_of_det_zero` contrapositive) ⇒ the det-1 matrix `[v | d⁻¹w]` sends the
  reference frame `([e₁],[e₂]) ↦ ([v],[w])`; compose `g₂∘g₁⁻¹` for general pairs;
  push SL→PSL via `pslPermHom_mk_smul`.

- ✅ **IwasawaStructure** `IwasawaStructure (PSL 2 q) ℙ¹` — `SL2.pslIwasawa`
  (DONE 2026-06-04).  `T x = Tline q x` = image in PSL of the transvection subgroup
  along the line `x` (`transvecGroup x.rep`).  `is_comm`: free (range of a CommGroup
  hom).  `is_conj` (`Tline_conj`): `transSL_conj` shows conjugating a transvection
  along `v` by `g ∈ SL` gives one along `g·v` *exactly* (no rescaling — because
  `det g = 1 ⇒ gᵀ⁻¹·vrot = (g·v)rot`), pushed through `mk'`.  `is_generator`
  (`Tline_iSup`): `transvecGroup e₁ = upper`s, `transvecGroup e₂ = lower`s
  (`transSL_e1/e2`), which generate SL (`transvections_generate`) hence PSL.
- ✅ **ASSEMBLY** `PSL2_isSimpleGroup` — feed all six into `PSL2_isSimpleGroup_of_iwasawa`.
- ✅ **ORDER PIN** (DONE 2026-06-04, axiom-clean): `card_center_SL2` (`|Z(SL(2,q))| = 2`
  for odd prime `q`, from `center_SL2 = {±1}` + `1 ≠ -1`) and `card_PSL2`
  (`|PSL(2,q)|·2 = q(q²−1)`, i.e. `q(q²−1)/2`, via Lagrange + `card_SL2`). `SL2Card.lean`
  is now wired into the build (imported by `SL2.lean`; was orphaned).

## E. ✅✅ FULLY DISCHARGED — `PSL(n,q)` simplicity, **axiom-clean** (done 2026-06-04)

**`PSL_isSimpleGroup` is now `[propext, Classical.choice, Quot.sound]`** — ZERO project
axioms. Both residual geometric axioms were discharged on 2026-06-04 (late lap):

1. **`SLn.exists_sl_maps_two_points`** (SL 2-transitive on ℙⁿ⁻¹) — **proved locally**
   (`SLnSimple.lean`). New construction (no reference frame): distinct points → indep reps
   (`rep_pair_li`); `exists_linearEquiv_pair` extends both pairs to bases via `Basis.sumExtend`
   and transports one onto the other with `Basis.equiv` (index sets equal cardinality =
   finrank), giving a linear iso `T u0=w0, T u1=w1`; corrected to det 1 by a `bw`-diagonal
   operator `D` scaling the `y1`-direction by `(det T)⁻¹`. `h2 : 2 ≤ |n|` kept but unused.
2. **`SLn.transvecSL_closure_eq_top`** (transvections generate SL) — **Aristotle proof
   (job `a4b84e9f`/`slngen`), verified clean in our kernel + ported** onto
   `SLnPerfect.transvecSL_closure_eq_top`. Whitehead via
   `Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec` + 5-transvection `diag(a,a⁻¹)`
   identity + strong induction on non-1 diagonal entries. Two v4.28→v4.29 port fixes:
   `det_elemDiag` (use `Finset.mul_prod_erase`), all-ones base case (`revert/rw/convert`).

**The entire PSL(n,q) thread is closed.** Nothing left here. See §F for the next thread.

### (historical) the two residuals, before discharge
`PSL_isSimpleGroup_rank_ge_three` was deleted from `LieType.lean`; the `n ≥ 3` case is the
machine-checked `SLn.PSLn_isSimpleGroup_of_rank` (`SLnIwasawa.lean`), wired into
`SL2.PSL_isSimpleGroup`.

**The entire Iwasawa criterion is assembled for general `n`** across `SLnAction/SLnSimple/
SLnIwasawa.lean` (all general `n : Type*`, `F` a field; specialised at `(Fin n, ZMod q)`):
perfect (`commutator_PSLn_eq_top`), nontrivial (`PSLn_nontrivial`), MulAction (`pslnAction`),
faithful (`pslnFaithful`/`pslnPermHom_injective`), quasi-preprimitive (`pslnQuasiPreprimitive`,
via `psln_two_pretransitive`), IwasawaStructure (`pslnIwasawaStructure`: the direction-`v`
transvection unipotent-radical family `Tline`, abelian + `is_conj` via `dirTransvecGroup_conj`
+ `is_generator` via `Tline_iSup`).

**ONLY TWO concrete geometric axioms remain** (both standard, both narrow):
1. **`SLn.transvecSL_closure_eq_top`** — transvections generate `SL(n,F)` (Whitehead/Gaussian).
   **OUT at Aristotle `a4b84e9f` (`slngen`)** — harvest next lap; mathlib has
   `Matrix.diagonal_transvection_induction`, missing only "det-1 diagonal = product of
   transvections". For `n=2` it's `SL2.transvections_generate`.
2. **`SLn.exists_sl_maps_two_points`** (`SLnSimple.lean`) — `SL(n,F)` 2-transitive on `ℙ^{n-1}`
   for `2 ≤ |n|`. Construction: distinct points → l.i. reps → `Basis.extend` to a basis →
   matrix with those as first two columns → rescale 2nd column by `1/det` (projectively
   invariant) ∈ SL. **NEXT Aristotle brick** (submit when `slngen` returns). `n=2` is
   `SL2.sl2_two_trans` (proved).

Discharging EITHER makes the corresponding obligation axiom-clean; discharging BOTH makes
`PSL_isSimpleGroup` fully `[propext, Classical.choice, Quot.sound]`.

### History (the build-up this lap)
Same Iwasawa pattern as `n = 2` but on `ℙ^{n-1}`. **`FiniteSimpleGroups/SLnPerfect.lean`:**
- ✅ `steinberg_comm` — the Steinberg/Chevalley relation `⁅t_{ik}(a),t_{kj}(b)⁆ =
  t_{ij}(ab)` (pairwise-distinct i,j,k), pure `Matrix.single` algebra, axiom-clean.
  (Cracked locally — beat the Aristotle job `4827df6e`, now ignored.)
- ✅ `transvecSL_mem_commutator` — **for `3 ≤ |n|`, every elementary transvection is a
  commutator in `SL(n,F)`**, axiom-clean. This is the genuinely-new n≥3 content: no
  field-size restriction (the `n=2` `|F|≥4` obstruction vanishes once a 3rd coordinate
  exists). Uses `steinberg_comm` + 3rd-index existence (`3 ≤ |n|`).
- ✅ `commutator_SLn_eq_top` — **`SL(n,F)` perfect for `3 ≤ |n|`**, modulo ONE disclosed
  axiom `transvecSL_closure_eq_top` (transvections generate `SL n F`). `#print axioms`
  = `[propext, Classical.choice, Quot.sound, transvecSL_closure_eq_top]`.

- ✅ **Iwasawa obligation 1 (perfect)** `commutator_PSLn_eq_top` — `PSL(n,F)` perfect for
  `3 ≤ |n|` (modulo the generation axiom), by descending `commutator_SLn_eq_top` along
  `SL ↠ SL/Z` (mirrors `SL2.PSL2_perfect`). `#print axioms` adds only
  `transvecSL_closure_eq_top`.
- ✅ **Iwasawa obligation 2 (nontrivial)** `PSLn_nontrivial` — `PSL(n,F)` nontrivial for
  `2 ≤ |n|`, axiom-clean. A transvection `t_{ij}(1)` is non-central (off-diagonal `(i,j)`
  entry `1`; central ⇒ scalar by mathlib `SpecialLinearGroup.mem_center_iff`).

**NB — mathlib already has the center characterization:** `Matrix.SpecialLinearGroup.mem_center_iff`
(`center = scalar matrices, scalars = n-th roots of unity`) and `center_equiv_rootsOfUnity'`.
Do NOT re-derive (one rule); cite these for the faithfulness/order obligations.

**⚠️ Action obligation needs a refactor:** the `SL(n,F) ↷ ℙ^{n-1}` action descends from the
linear `mulVec` action, but `SL2.lean` already declares `SMul/MulAction/DistribMulAction/
SMulCommClass (SL (Fin 2) F) (Fin 2 → F)` instances. Declaring the **general-`n`** versions
would create instance diamonds at `Fin 2`. Fix: extract the general `mulVec` action instances
into a shared file (e.g. `SLnAction.lean`) and have `SL2.lean` import/reuse them, then build the
ℙ^{n-1} descent on top. Deliberate refactor — do fresh, not late-lap.

All five Iwasawa obligations above the two residual geometric axioms are now ✅ DONE and
committed (SLnAction action refactor; SLnSimple center-acts-trivially/faithful/quasi-prep;
SLnIwasawa direction-`v` transvection algebra → subgroup → `Tline` → record → assembly).

**OTHER candidate discharges, lower priority:**
- **`alternatingGroup_isSimple`** — BLOCKED: bucket C (mathlib `Alternating/Simple.lean`
  / `alternatingGroup.isSimpleGroup` post-dates v4.29.1 pin; only `isSimpleGroup_five`
  present). Discharge = bump the pin, NOT re-derive (the one rule). Confirmed absent
  from `.lake/packages/mathlib` 2026-06-04.
- **Sporadic / exceptional / CFSG-milestone axioms** — deep, intended-permanent (§B).
  Order-pin faithfulness anchors are the tractable surface there (RFI resolved).

**Aristotle:** `card_SL2` (`|SL(2,q)| = q(q²-1)`, job `28df03ca`) — DONE & ported
(`aceed22`); useful for `|PSL(2,q)|` and the order tables.

## F. ✅✅✅ — `PSp_{2n}(q)` simplicity: **FULLY AXIOM-CLEAN for ALL valid (n,q)** (2026-06-04)

**HEADLINE (2026-06-04, latest lap — DONE):** The ENTIRE symplectic family simplicity is now
machine-checked from first principles with ZERO custom axioms:
- `#print axioms PSp_isSimpleGroup` = `[propext, Classical.choice, Quot.sound]`.
- `#print axioms PSpn_isSimpleGroup_of_iwasawa` = `[propext, Classical.choice, Quot.sound]`.

The last residual `PSp_perfect_small_field` (perfectness for `q∈{2,3}`) is now a **theorem**
(see F.0). Two complementary type-`Cₙ` Steinberg engines in `SpSmallField.lean`:
- **n=2 (⟹ q=3, char≠2):** `commutator_PSp_eq_top_char_ne_two` — `τ_{eᵢ,c}=⁅1+s·N₁,1+N₂⁆`,
  structure constant `2` invertible. Built on `mem_one_add_rootN1/2` (symplectic membership via
  the `vecMulVec`/`J`-on-basis algebra), `inv_one_add_smul`, `one_add_rootM_eq_spTransvection`.
- **n≥3 (ANY field, char-free):** `commutator_PSp_eq_top_n3` — the rank-3 relations
  `rootN1_steinberg`/`rootN2_steinberg` (const ±1) + `rootM_steinberg`
  (`⁅1+N₁(i,j),1+a·M_j⁆ = (1+a·N₂(i,j))·τ_{eᵢ,·}`, long-root coeff **1**, survives char 2). Generic
  helpers `group_comm_first_order`/`group_comm_second_order`. This is what makes `Sp(2n,2)` perfect.

`SpLieType.PSp_perfect_small_field` dispatches n<3→char≠2, n≥3→rank-3. `PSp(4,2)≅S₆` excluded.

**THE SYMPLECTIC FAMILY IS CLOSED. Next deep thread: PSU (§G below).**

This lap discharged BOTH former core axioms and wired into LieType:
1. **Primitivity `psp_isTrivialBlock_of_isBlock` → THEOREM.** Block combinatorics machine-checked:
   T1 non-perp transitivity (`psp_stab_maps_nonperp`, from `exists_sp_transvecFixing_maps_mate`),
   connectivity of the non-orthogonality graph (`exists_form_both_ne`), rank-3 bootstrap. Reduced
   to a single Δ₀ statement, then…
2. **Δ₀ transitivity `sp_stab_transitive_on_perp_lines` → THEOREM** (beat Aristotle `91082bf9`,
   cancelled). KEY: all transvections centred in the *full* `v^⊥` fix `v` (the earlier
   "unipotent radical" worry was over-constraining by fixing a whole pair); `sp_transvecFixing_step`
   (e=v) maps `u→u'` directly — one transvection if `ω(u,u')≠0`, else through `w∈v^⊥` non-orth to
   both (`exists_form_both_ne_in_perp` ← `exists_dot_both_ne_perp`, field-size-free).
3. **Wired into LieType** (`SpLieType.lean`): old monolithic `axiom PSp_isSimpleGroup` removed;
   now a theorem with `[Fact (Nat.Prime q)]` (composite-q soundness fix). `q≥5` ⇒ machine-checked
   Iwasawa (via `exists_sq_ne_one`, λ=2); `q∈{2,3}` ⇒ the residual.
4. **Residual narrowed to PERFECTNESS.** `PSpn_isSimpleGroup_of_perfect` takes `commutator=⊤` as
   hypothesis (faithfulness + quasi-primitivity hold over ANY field). So the sole remaining PSp
   axiom is `PSp_perfect_small_field` : `commutator (PSp n q) = ⊤` for `q∈{2,3}`, `n≥2`,
   `¬(n=2∧q=2)`. `PSp(4,2)≅S₆` correctly excluded — it fails at perfectness, not primitivity.

### G. ◐ ACTIVE DEEP THREAD — `PSU_{n}(q)` simplicity (the unitary family)
**Status:** `PSU n q` is still `opaque` in `LieType.lean` (NOT connected to a concrete group), so
`axiom PSU_isSimpleGroup (n q)(3≤n)` is vacuous-ish. Discharging it is genuinely multi-lap.
**Steps 0, 1, and the step-2 number-theory prereqs are DONE (2026-06-04 PM).**

- ✅ **Step 0 (foundation)** — `UnitaryFoundation.lean`. `UnitaryField p := GaloisField p 2`,
  `star = frobenius` (`star x = x^p`), `StarRing` on the type synonym; `SU n p`, `PSUConcrete`.
- ✅ **Step 1 (transvections) — COMPLETE** in `UnitaryTransvection.lean` (general `[CommRing α]
  [StarRing α]`), all axiom-clean (`[propext, Classical.choice, Quot.sound]`):
  - `uTransvection v a := 1 + a•(v ⊗ star v)`; `uTransvection_mulVec` (action `x ↦ x+a⟨v,x⟩v`).
  - `uTransvection_star : star τ_{v,a} = τ_{v,star a}` (`v⊗star v` Hermitian) ⟹
    `uTransvection_mem` (∈ unitaryGroup iff `v` isotropic `star v⬝ᵥv=0` ∧ `a` trace-zero
    `a+star a=0`), `uTransvection_det = 1`, `uTransvection_mem_su` (∈ specialUnitaryGroup).
  - `uTransvection_mul : τ_{v,a}τ_{v,b}=τ_{v,a+b}` (isotropic); `u_preserves_form`,
    `u_isotropic_of_mem`; `uTransvection_conjH/conj : gτ_{v,a}g⁻¹=τ_{g·v,a}`.
  - **Perfectness engine:** `uTransvection_smul_vec : τ_{c·v,a}=τ_{v,a·(c·star c)}` (NORM replaces
    square), `uTransvection_inv_eq`, `uTransvection_commutator : [g,τ_{v,a}]=τ_{v,(N(λ)−1)·a}`
    when `g·v=λ·v` (N(λ)=λ·star λ).
  - **Group level:** `traceZero α : AddSubgroup` (skew-Hermitian scalars), `uTransvecHom :
    Multiplicative(traceZero α)→*SU`, `uRootSubgroup v` (= range, abelian via `IsMulCommutative`),
    `uTransvecSU_conj` (the Iwasawa `is_conj` input).
- ✅ **Step 2 number-theory prereqs — DONE** in `UnitaryFoundation.lean`, all axiom-clean:
  - `Algebra (ZMod p) (UnitaryField p)`; `algebraMap_norm_eq_mul_star : algebraMap(norm c)=c·star c`
    (both `c^{p+1}`); `exists_norm_neg_one : ∃ c, c·star c=−1` (via `FiniteField.norm_surjective`).
  - `exists_isotropic (n≥2) : ∃ v≠0, star v⬝ᵥv=0` (`v=c·e₀+e₁`) — Iwasawa-action NONEMPTINESS.
  - `exists_traceZero_ne_zero : ∃ a≠0, a+star a=0` (Frobenius nontrivial via
    `orderOf_frobeniusAlgHom=finrank=2`) — `uRootSubgroup` NONTRIVIALITY.

- ✅ **Step 2 FAITHFULNESS (kernel = center) — FULLY AXIOM-FREE** (2026-06-04 PM/eve,
  `UnitarySimple.lean`). The crux `g∈SU fixing every isotropic line ⟹ scalar` is machine-checked:
  - `su_fixes_isotropic_imp_scalar` (AXIOM-CLEAN): proved from geometry facts as hypotheses, via
    the form-relation engine `lambda_form_relation` + the **hyperbolic-pair collapse**
    `lambda_eq_norm_one_of_hyperbolic` (trace-zero sum trick: `v+s·w` isotropic ⟹ `λ_v=λ_w` AND
    `N(λ_v)=1`) + `lambda_eq_of_nonorth`, propagating one scalar `μ` through connectivity and
    across the spanning set.
  - `su_central_fixes_isotropic_line` (center⊆fixes, via `uTransvecSU_conj`),
    `su_center_le_scalar` / `su_scalar_mem_center` / `su_mem_center_iff_scalar` (center = scalars,
    `n≥3`), `su_fixes_isotropic_imp_central` (ker⊆center half), `PSU_nontrivial` (Iwasawa
    `Nontrivial` obligation), and the SU-action on `n→F` / `ℙ(Fⁿ)`.
  - Geometry facts: ALL THREE **DISCHARGED** (axiom-clean). `isotropic_span` +
    `exists_hyperbolic_partner` (new `UnitaryFoundation` lemmas `exists_star_ne_self`,
    `exists_two_norm_neg_one`, `algebraMap_trace_eq_add_star`, `exists_add_star_eq_neg_norm`); and
    `exists_common_nonorth_isotropic` (diameter-2 connectivity). The last brick — the perpendicular
    case `common_nonorth_isotropic_perp` — was discharged 2026-06-04 eve **without any H^⊥
    machinery**: project any partner `w₂` of `z₂` into `H^⊥` (`w₂' = w₂ - α·z₁ - β·w₁`), then
    re-isotropize with the *explicit* scalar `t = α·star β` (works because the projected
    self-product `⟨w₂',w₂'⟩ = -(α·star β + β·star α)` is automatically of the form `-(x+star x)`).
    Then `u = w₁ + w₂'' ` is the common non-orthogonal isotropic. `#print axioms su_center_le_scalar`
    / `su_mem_center_iff_scalar` = `[propext, Classical.choice, Quot.sound]`. **The entire kernel=center
    half of step-2 faithfulness is now axiom-free.**
- ✅ **Step 2 FAITHFUL ACTION — DONE** (2026-06-04 eve, `UnitarySimple.lean` §Faithful, axiom-clean).
  Built the SU-action on the ISOTROPIC ℙ-points subtype `IsoPoint p n` (not full ℙ — PSU isn't
  transitive there): `instSMulIsoPoint`/`instMulActionIsoPoint` (`su_smul_isoPoint_mem` = form
  preserves isotropy; `isIso_mk_iff` = isotropy well-defined on ℙ via `star_smul_dotProduct_self`).
  Wired `su_central_fixes_isotropic_line` ⟹ `su_center_le_isoKer` (center ⊆ ker) and
  `su_fixes_isotropic_imp_central` ⟹ `su_isoKer_le_center` (ker ⊆ center); descended through the
  center to `psuPermHom : PSUConcrete →* Perm IsoPoint`, proved `psuPermHom_injective` (n≥3) and
  **`psuFaithful : FaithfulSMul (PSUConcrete n p) (IsoPoint p n)`** — the Iwasawa `FaithfulSMul`
  obligation. `#print axioms psuFaithful` = `[propext, Classical.choice, Quot.sound]`. Mirrors
  `SpN.pspFaithful`/`pspPermHom`/`pspAction` line-for-line.
- **Step 2c REMAINING — quasi-preprimitivity** of the `IsoPoint` action (the deep geometric core,
  mirrors SpIwasawa's `psp_isTrivialBlock_of_isBlock`). Mathlib has `IsPreprimitive.isQuasiPreprimitive`.
  Needs: SU transitive on isotropic points (Witt) + blocks are trivial.
- **Step 3a — generation.** Unitary transvections generate `SU` (the unitary Eichler/Witt
  theorem). DEEP core, mirrors `sp_stab_hyperbolic_le` / the ambient-induction generation proof.
  **Submitted to Aristotle 2026-06-04 eve (project `a1c167e7-c1bb-417e-9dd2-15e82ddd1fc4`)** as a
  self-contained `import Mathlib` stub (`/tmp/aristotle-ugen/UGen.lean`): transvections generate
  `SU_n(F)` for `3 ≤ card n`, with `uTransvection_mem_su` as the one supplied axiom.
- ✅ **Step 3b — SCALING ELEMENT DONE** (2026-06-04 eve, `UnitaryTransvection.lean` §Scaling). The
  `spDiag` analogue is fully machine-checked (all `[propext, Classical.choice, Quot.sound]`):
  `uScale v w λ := 1 + (λ-1)·(v⊗star w) + ((star λ)⁻¹-1)·(w⊗star v)` on a hyperbolic pair `(v,w)`;
  `uScale_mulVec_self` (`v↦λ·v`), `uScale_mem` (`∈ U`, via `A²=A,B²=B,AB=BA=0`), `uScale_det`
  (`det = λ·(star λ)⁻¹`, via Weinstein–Aronszajn `det_one_add_mul_comm` + 2×2 `det_fin_two`),
  `uScale_mem_su` (`∈ SU` when `star λ = λ`, the fixed field, so `det = λ·λ⁻¹ = 1`). The hyperbolic
  partner `w` comes from the proven `exists_hyperbolic_partner` — no generation needed for the
  element. ✅ **(i) `uTransvecSU_mem_commutator` DONE** (2026-06-04 eve, axiom-clean): each unitary
  transvection `τ_{v,a} = ⁅uScale v w λ, τ_{v, a/(N(λ)-1)}⁆ ∈ commutator(SU)`, given a hyperbolic
  pair and a fixed-field `λ` with `N(λ) = λ·star λ ≠ 1` (mirrors `spTransvecSp_mem_commutator`).
  ✅ **(ii) PERFECTNESS ENGINE DONE** (axiom-clean): `commutator_specialUnitaryGroup_eq_top`
  (field-generic, takes generation + fixed-field `λ` + hyperbolic partners as hyps) AND the concrete
  `commutator_SU_eq_top_of_generate` (n≥3, p≥5, in `UnitarySimple.lean`) which feeds in the proven
  `UnitaryField.exists_fixedField_norm_ne_one` (p≥5) + `exists_hyperbolic_partner`. **The ONLY
  remaining input for `commutator(SU)=⊤` is generation** (Step 3a — Aristotle project
  `a1c167e7-c1bb-417e-9dd2-15e82ddd1fc4`, IN_PROGRESS). (iii) descend `commutator=⊤` to
  `PSUConcrete` (quotient is perfect if `SU` is — `commutator` surjects). CAUTION: small exceptions
  (e.g. SU(3,2) not perfect) handled by the `p≥5` hyp; the exact exclusion is deferred. For general
  (non-fixed-field) `λ`, multiply `uScale` by a norm-1 `μ=(star λ)λ⁻¹` on the complement (n≥3, TODO).
- **Step 3c — assemble** `MulAction.IwasawaStructure` (same mathlib criterion) ⟹
  `IsSimpleGroup (PSUConcrete n p)`. **HAVE (this lap):** `psuFaithful` (FaithfulSMul on
  `IsoPoint p n`), `PSU_nontrivial` (Nontrivial), `nonempty_isoPoint` (action set nonempty),
  perfectness engine (above). **NEED:** the `IwasawaStructure` T-family `Tline : IsoPoint → Subgroup
  PSUConcrete` (= `uRootSubgroup` descended through center) with `is_comm` (abelian — `uRootSubgroup`
  is `IsMulCommutative`), `is_conj` (conjugation-equivariant — mirror `pspIwasawaStructure.is_conj`
  using `uTransvecSU_conj`), `is_generator` (= generation, Step 3a); and **`IsQuasiPreprimitive`**
  of the `IsoPoint` action (DEEP — unitary Witt transitivity + trivial blocks, mirror SpIwasawa
  `pspQuasiPreprimitive`). Then **connect `LieType.PSU`** (replace `opaque` carrier; general `q=p^m`
  needs `GaloisField p (2m)` + `iterateFrobenius`).
The whole PSp scaffold (`SpIwasawa`/`SpTransvection`/`SpSmallField`) remains the template to copy.

**Aristotle in flight (2026-06-04 eve):** unitary Witt generation (project
`a1c167e7-c1bb-417e-9dd2-15e82ddd1fc4`, stub `/tmp/aristotle-ugen/UGen.lean`). Poll with
`aristotle tasks a1c167e7-c1bb-417e-9dd2-15e82ddd1fc4`. (The scaling-element brick is now DONE
locally — see Step 3b.)

**Other open classical axiom:** `POmega_isSimpleGroup` (n≥7) — also opaque, orthogonal geometry,
hardest of the four (ε-type quadratic forms). After PSU.
**NOT worth manual effort:** `alternatingGroup_isSimple` (general Aₙ) is a **pin-lag artifact** —
landed in mathlib PR #36524, 11 days past our pin; collapses to a one-liner on `lake update`
(corpus `mathlib-alternating-simple-pin-lag.md`). `SmallOrders.lean:104` (simple <60 ⟹ prime) is
genuinely absent from mathlib but optional scaffold, not a blocker.

### F.0 ✅ DONE — `PSp_perfect_small_field` (perfectness for q∈{2,3}) — NOW A THEOREM
Discharged this lap (see F headline). The historical plan below is kept for reference.
The genuine remaining core. PSp(2n,q) is perfect except Sp(2,2),Sp(2,3),Sp(4,2) (all excluded by
`n≥2 ∧ ¬(n=2∧q=2)`). The `λ²≠1` commutator engine (`[g,τ_{v,a}]=τ_{v,(λ²-1)a}`) is useless for
q∈{2,3} (no such λ). Needs the **symplectic Steinberg/Chevalley root relations** (type `C_n`):
- Short-root unipotents `x_{εᵢ-εⱼ}(s)=1+s·N₁`, `x_{εᵢ+εⱼ}(t)=1+t·N₂` with, for `i≠j` (standard
  basis `eᵢ=single(inr i)`, `fᵢ=single(inl i)`): `N₁ = E_{eᵢ,eⱼ} − E_{fⱼ,fᵢ}`,
  `N₂ = E_{eᵢ,fⱼ} + E_{eⱼ,fᵢ}` (`E_{a,b}=Matrix.single a b 1`).
- **Long-root commutator:** `N₁N₂ = E_{eᵢ,fᵢ} =: M`, `N₂N₁ = −M`, so `[N₁,N₂]=2M`, giving
  `[1+sN₁, 1+tN₂] = 1 + 2st·M = x_{2εᵢ}(2st)` (the long-root transvection `τ_{eᵢ,·}`). The
  **structure constant 2** is exactly why char 2 (`Sp(4,2)`) fails and char 3 (`Sp(4,3)`) works.
- **q=3 (char 3):** 2≠0, so `τ_{eᵢ,c}` is a commutator (2st covers all c) → long roots in
  `commutator`. For `n≥2` also need short roots ∈ commutator (`[x_{εᵢ-εⱼ},x_{εⱼ-εₖ}]=x_{εᵢ-εₖ}`
  needs a 3rd index ⇒ `n≥3`; for `n=2` use `[x_{2εⱼ},x_{εᵢ-εⱼ}]=x_{εᵢ+εⱼ}` long+short). Then
  generation (`sp_transvec_closure_eq_top`, HAVE) ⇒ `commutator=⊤`.
- **q=2 (char 2, n≥3):** long-root coefficient 2 vanishes; perfectness comes from short roots
  being mutual commutators (coefficient ±1, char-free) + the fact `Sp(2n,2)` is generated by
  short+long and long roots are reached differently. Subtler — Sp(4,2) genuinely not perfect.
- **Attack:** (a) abstract `unipotent_commutator` identity — OUT at Aristotle `61d28cfc`
  (`aristotle-sympstein`); (b) instantiate `N₁,N₂,M` as the matrix units, prove the 9 relations
  via `Matrix.single_mul_single_same`/`_of_ne` (`i≠j`); (c) symplectic membership of `1+sN₁`,
  `1+sN₂` via `sp_preserves_form`; (d) wrap into `commutator_Sp_eq_top_small` and descend to
  `commutator_PSp` ⇒ discharge `PSp_perfect_small_field`. Multi-lap; q=3 first.

### F.1 (historical) Iwasawa REDUCED to 1 disclosed axiom (earlier 2026-06-04)

**GENERATION CORE `sp_stab_hyperbolic_le` FULLY DISCHARGED.**
`#print axioms PSpn_isSimpleGroup_of_iwasawa` = `[propext, Classical.choice, Quot.sound,
psp_isTrivialBlock_of_isBlock]` — **down to ONE core axiom.** `sp_transvec_closure_eq_top`
(symplectic transvections generate `Sp`) is now `[propext, Classical.choice, Quot.sound]`,
machine-checked via the **ambient standard-basis induction** (the design recorded below): the
`offS S` perp toolkit (`offS_form_nondeg`/`offS_form_both_ne`/`offS_transvecGen_maps`/
`offS_transvecFixing_maps_mate`/`offS_transvecGen_maps_pair`) + `FixS`/`offS_preserved` +
`sp_eq_one_of_FixS_univ` + the strong induction `genAux_le` on `Sᶜ.card`. All in `SpIwasawa.lean`.
The old `axiom sp_stab_hyperbolic_le` and the perp-of-one-pair toolkit (`perpComp` etc.) are now
superseded/dead (kept for the record). **The Aristotle `8522edf3` (spstab) bare-stub job is now
MOOT** — this local proof beat it. **ONLY REMAINING PSp axiom: `psp_isTrivialBlock_of_isBlock`
(primitivity core, §F.2 below).** That is now the highest-value PSp target.

## F (historical). `PSp_{2n}(q)` simplicity: Iwasawa REDUCED to 2 disclosed axioms (2026-06-04 PM)

**`PSp n q`** in `LieType.lean` = `symplecticGroup (Fin n) (ZMod q) ⧸ center` (mathlib's
`Matrix.symplecticGroup`, form `J = fromBlocks 0 (-1) 1 0` on `(Fin n ⊕ Fin n)`).
`axiom PSp_isSimpleGroup (n q) (2 ≤ n) (¬(n=2∧q=2))` is the LieType target (NOT yet wired to
`PSpn_isSimpleGroup_of_iwasawa`).

**HEADLINE (2026-06-04 PM lap):** `SpN.PSpn_isSimpleGroup_of_iwasawa [Nonempty l]
(hlam : ∃ lam:F, lam≠0 ∧ lam²≠1) : IsSimpleGroup (symplecticGroup l F ⧸ center)`.
`#print axioms` = `[propext, Classical.choice, Quot.sound, pspQuasiPreprimitive,
sp_stab_hyperbolic_le]` — **down from 3 deep axioms to 2.** This lap:
- **Perfectness DISCHARGED.** `commutator_PSp_eq_top` is now a THEOREM. The deep "PSp perfect"
  axiom was replaced by the elementary `sp_scaling_exists`, which was THEN ALSO discharged
  (see next). Engine: `spTransvecSp_commutator` `[g,τ_{v,a}]=τ_{v,(λ²-1)a}` when `g·v=λv`,
  so `τ_{v,c}=⁅g,τ_{v,c/(λ²-1)}⁆∈commutator` when `λ²≠1`. The `hlam` (∃λ≠0,λ²≠1, i.e. |F|≥4)
  hypothesis is the HONEST field-size condition — it now correctly EXCLUDES the non-simple
  `PSp(4,2)≅S₆` (the old axiom unsoundly claimed it simple/perfect).
- **Scaling DISCHARGED.** `sp_scaling_exists` (∀v≠0,λ≠0 ∃g∈Sp: g·v=λv) is a machine-checked
  THEOREM: `spDiag λ = fromBlocks (λ•1) 0 0 (λ⁻¹•1)` is symplectic (`spDiag_mem`) and scales
  `inl`-vectors by λ; conjugate by a transvection product (transitivity) to scale any v.
- **Generation NARROWED.** `sp_transvec_closure_eq_top` is now a THEOREM resting only on the new
  core axiom `sp_stab_hyperbolic_le`. The whole transitivity machinery is machine-checked:
  `exists_sp_transvecGen_maps` (Sp transitive on nonzero vectors via transvections — both the
  ω≠0 single-transvection case and the orthogonal-case z-bridge),
  `exists_sp_transvecFixing_maps_mate` (transvections fixing e transitive on e's hyperbolic
  mates, no field-size hyp — degenerate case routed through f''=f'+e),
  `exists_sp_transvecGen_maps_pair` (Sp transitive on hyperbolic pairs via `sp_preserves_form`).

**REFINED ATTACK ON CORE 1 (2026-06-04 PM, this lap) — the ambient standard-basis induction.**
Sidesteps BOTH the abstract-submodule layer AND the subtype/reindex transport. Key insight: use
the **standard hyperbolic pairs** `e_i := single(inr i)`, `f_i := single(inl i)` (`ω(e_i,f_i)=1`
under `J = fromBlocks 0 (-1) 1 0`). Then the perp of a coordinate set `S : Finset l` is the clean
coordinate subspace `offS S := {x : ∀ i∈S, x(inl i)=0 ∧ x(inr i)=0}`, and:
  - **relative non-degeneracy is DIRECT coordinate algebra** (no iterated `perpComp`): `x∈offS S`,
    `x≠0` ⟹ some off-`S` coord `p` has `x p≠0`; the matching standard basis vector (`single(inr j)`
    or `single(inl j)`, `j∉S`) is in `offS S` and `ω`-pairs with `x` (`ω(x,single(inr j))=-x(inl j)`,
    `ω(x,single(inl j))=x(inr j)`).
  - **transvection centred in `offS S` fixes every `S`-pair** (`single(inl i)⬝ᵥJv=-v(inr i)=0`,
    `single(inr i)⬝ᵥJv=v(inl i)=0` for `i∈S`).
  - **`g` fixing all `S`-pairs preserves `offS S`** via `sp_preserves_form`
    (`(g·x)(inl i)=ω(single(inr i),g·x)=ω(single(inr i),x)=x(inl i)=0`).
This makes the WHOLE generation theorem fall out of ONE induction on `Sᶜ.card`, proving
`genAux S g (∀i∈S, g fixes pair i) : g∈⟨transvecs⟩` and instantiating at `S=∅` ⟹ **eliminates
`sp_stab_hyperbolic_le` entirely** (`sp_transvec_closure_eq_top := genAux ∅`). Step: pick `i₁∉S`,
map the hyperbolic pair `(g·e_{i₁},g·f_{i₁})` (in `offS S`) back to `(e_{i₁},f_{i₁})` by `t∈⟨transvecs⟩`
fixing `S`-pairs (`offS`-relative transitivity on hyperbolic pairs), so `t·g` fixes `S∪{i₁}`, IH.
Base `S=univ`: `g` fixes all standard basis vecs ⟹ `g=1` (`(g*ᵥsingle p)_q=g q p=δ`). Lemmas to
build (each a faithful `offS`-mirror of an existing `⟨e,f⟩⊥` lemma): `offS_form_nondeg`,
`offS_form_both_ne`, `offS_transvecGen_maps` (vectors), `offS_transvecFixing_maps_mate`,
`offS_transvecGen_maps_pair`, `offS_preserved`, the base, the strong-induction wiring.
Developing in scratch `/tmp/spgen` (imports SpIwasawa), port + replace axiom when green.

**THE TWO REMAINING DISCLOSED AXIOMS (attack paths):**
1. **`sp_stab_hyperbolic_le`** (generation core) — a symplectic `g` fixing a hyperbolic pair
   `(e,f)` (`ω(e,f)=1`) pointwise lies in `⨆_v spTransvecGroup v`. The **dimension induction**:
   `g` restricts to `Sp` on `⟨e,f⟩⊥`, where transvections generate. **COMPLEMENT INFRASTRUCTURE
   NOW COMPLETE & machine-checked** (all in `SpIwasawa.lean`, the path-(ii) coordinate route — NO
   abstract recursion needed):
   - `perpComp e f x = x + ω(f,x)·e − ω(e,x)·f`, `perpComp_mem_perp`, `perpComp_add_span` — the
     explicit `V = ⟨e,f⟩ ⊕ ⟨e,f⟩⊥` decomposition on coordinates.
   - `spForm_nondegenerate` (global) + `perp_form_ne_of_mem_perp` (relative non-degeneracy on
     `⟨e,f⟩⊥`).
   - `exists_perp_form_both_ne` + `exists_perp_transvecGen_maps` — **transitivity within `⟨e,f⟩⊥`
     by pair-fixing transvections** (the inductive engine: maps any `u→w` in `⟨e,f⟩⊥` by transvecs
     that fix `(e,f)`).
   - `sp_fixing_preserves_perp` (`g` preserves `⟨e,f⟩⊥`), `spTransvection_fixes_pair` (extend back).
   **THE ONLY REMAINING GAP**: the induction *bookkeeping/termination* — iterate
   `exists_perp_transvecGen_maps` to reduce `g|_⟨e,f⟩⊥` to the identity, with a well-founded
   measure (the dimension/rank of the subspace where `g ≠ id`, decreasing by ≥1 each step). Likely
   shape: strong induction on `Fintype.card l`, OR a measure on `Module.rank` of `ker(g-1)ᶜ`. The
   geometric content is all done; this is the formalization of "peel off one fixed hyperbolic pair
   at a time". Aristotle job `8522edf3-fdae-4924-9549-2eb53e1a8f50` (bare-statement stub, no infra)
   still IN_PROGRESS at lap end — POLL `aristotle tasks <uuid>`; if it walled, RESUBMIT with the
   complement lemmas above inlined as a richer stub.
2. **`psp_isTrivialBlock_of_isBlock`** (primitivity core — THE only remaining PSp axiom). `PSp`
   transitive on ℙ²ⁿ⁻¹ (`psp_isPretransitive`, proven) but **NOT 2-transitive** (preserves `ω`),
   so blocks-trivial needs the rank-3 / maximal-parabolic argument. **Concrete attack plan
   (2026-06-04):**
   - **Reduce** to the based form via mathlib `IsPreprimitive.of_isTrivialBlock_base a₀`: suffices
     blocks `B ∋ a₀` are trivial (`a₀ = [single(inl i₀)]`). A block `B ∋ a₀` is automatically
     `Stab(a₀)`-invariant (mathlib `IsBlock.smul_eq_of_mem`: `a₀ = g•a₀ ∈ g•B ∩ B ⟹ g•B = B`).
   - **Orbit structure of `Stab([v₀])` on ℙ(V)** (rank 3, n≥2): `{[v₀]}`, `Δ₀ = {[u] : ω(v₀,u)=0}`
     (perp lines ≠ [v₀]), `Δ₁ = {[w] : ω(v₀,w)≠0}` (non-perp). So a `Stab`-invariant `B ∋ [v₀]` is
     a union of these. Need: (i) **`Δ₁` transitivity** — EASY, already available: it is exactly
     `exists_sp_transvecFixing_maps_mate` (e=v₀,f=w,f'=w' after scaling ω=1, g fixes v₀, g·w=w').
     (ii) **`Δ₀` transitivity** — the perp-line Witt transitivity (stabiliser of v₀ transitive on
     lines in v₀⊥∖⟨v₀⟩). **OUT at Aristotle `91082bf9` (`aristotle-perpwitt`, vector-level stub
     with the offS/pair transitivity inlined as axioms).** Or prove locally via the offS toolkit:
     extend v₀ to a hyperbolic pair (v₀,w), decompose u = α·v₀ + u_perp (ω(v₀,u)=0 ⟹ no w-part),
     map u_perp→u'_perp within ⟨v₀,w⟩⊥ by pair-fixing transvecs, fix the α via τ_{v₀,·}.
   - **Bootstrap to univ** (rank-3 connectivity): if `B ⊋ {[v₀]}` then B ⊇ Δ₀ or Δ₁; show either
     forces B=univ. From a non-perp [w]∈B (w=g·v₀ for some g, [w]∈Δ₁⊆B) get g·B=B (block + [w]∈B),
     so B is invariant under {g : g·[v₀]∈B}; the non-perp graph (and perp graph) on ℙ(V) is
     connected for n≥2 (any two lines joined by a chain of perp/non-perp steps), forcing B=univ.
     This combinatorial bootstrap is the genuine remaining content — good next-lap local target,
     OR an Aristotle brick once Δ₀ transitivity lands. `n=1` (PSp(2,q)=PSL(2,q)) is 2-transitive
     hence primitive trivially (separate easy case if needed).
   - Tools: mathlib `GroupTheory/GroupAction/Primitive.lean` (`of_isTrivialBlock_base`,
     `isCoatom_stabilizer_iff_preprimitive`) + `Blocks.lean` (`IsBlock.smul_eq_of_mem`, `IsBlock.orbit`).
     The repo already has `pspPreprimitive_iff_isCoatom_stabilizer` (maximal-subgroup form).

**Files** — `SpTransvection.lean` (transvection algebra + `sp_preserves_form`,
`spTransvecSp_commutator`, `spTransvecSp_inv`, `_apply_self`/`_apply_of_orth`),
`SpAction.lean`, `SpSimple.lean` (faithfulness), `SpIwasawa.lean` (ALL the transitivity
lemmas, perfectness chain, `spDiag`+`sp_scaling_exists`, generation reduction, the 2 axioms,
assembly). All machine-checked except the 2 axioms.

**NEXT LAP:** the ONLY remaining PSp core is `psp_isTrivialBlock_of_isBlock` (primitivity).
(a) Harvest Aristotle `91082bf9` (`aristotle-perpwitt`, the Δ₀ perp-line transitivity) if returned
— verify in-kernel + `#print axioms`, port onto repo defs; if it walled, prove Δ₀ transitivity
locally via the offS toolkit (decompose `u = α·v₀ + u_perp`, see §F.2). (b) Then build the
rank-3 **bootstrap** (block ∋ [v₀] containing a perp/non-perp neighbour ⟹ univ) using mathlib's
block API — the genuine remaining content. (c) AFTER primitivity lands, WIRE
`PSpn_isSimpleGroup_of_iwasawa` into LieType's `PSp_isSimpleGroup` (specialise `l:=Fin n`,
`F:=ZMod q`, supply `hlam` from `q≥5`; the `hlam`/|F|≥4 route MISSES `q∈{2,3}` — PSp(2n,3) is
simple but needs a separate perfectness argument, so leave a `q∈{2,3}` residual axiom, mirroring
the PSL n=2/n≥3 split).

## C. Soundness-audit TODO (cheap, valuable — flagged 2026-06-03)

The Bender axiom once slipped in **false**.  Re-read each `axiom`'s *statement* for faithfulness:
the `IsFSG`-typeclass milestone axioms have complex conclusions worth a careful read.  The newly
added `isSimpleGroup_centralizer_index_not_primePow` was audited this lap (true: it is exactly
Burnside's lemma; abelian-simple = prime-cyclic gives index 1 = `p^0`, excluded by `k ≥ 1`).

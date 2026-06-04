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

## E. ✅ DISCHARGED — `PSL(n,q)` simplicity for `n ≥ 3` via Iwasawa (done 2026-06-04)

**`PSL_isSimpleGroup_rank_ge_three` is GONE** — deleted from `LieType.lean`; the `n ≥ 3` case
is now a machine-checked theorem `SLn.PSLn_isSimpleGroup_of_rank` (`SLnIwasawa.lean`), wired
into `SL2.PSL_isSimpleGroup`. `#print axioms FiniteSimpleGroups.PSL_isSimpleGroup` =
`[propext, Classical.choice, Quot.sound, SLn.exists_sl_maps_two_points,
SLn.transvecSL_closure_eq_top]`.

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

## C. Soundness-audit TODO (cheap, valuable — flagged 2026-06-03)

The Bender axiom once slipped in **false**.  Re-read each `axiom`'s *statement* for faithfulness:
the `IsFSG`-typeclass milestone axioms have complex conclusions worth a careful read.  The newly
added `isSimpleGroup_centralizer_index_not_primePow` was audited this lap (true: it is exactly
Burnside's lemma; abelian-simple = prime-cyclic gives index 1 = `p^0`, excluded by `k ≥ 1`).

# CFSG scaffold — the work map 🗺️

*Built 2026-05-31. The single source of truth for "what is real work here vs what
is not." Re-derive nothing that is formalized elsewhere — that is the whole point.*

## The one rule

This repo builds the **Classification of Finite Simple Groups as a Lean
scaffold**. CFSG-as-a-whole is formalized *nowhere*, so the **architecture**
(stating the theorem + its dichotomy/reduction structure, wiring proven
reductions on top of honest axioms) is the genuine novel contribution.

**We only spend effort on work that is BOTH (a) part of the CFSG scaffold AND
(b) not already formalized somewhere else.** Everything formalized elsewhere —
in mathlib (any version) or in the MathComp/Coq Feit–Thompson proof — is either
deleted-on-bump or left as an honest axiom. We never re-derive it.

## The four buckets

Every `axiom`/`sorry`/theorem in the repo falls into exactly one:

### 🟩 A — DONE (proven, sorry-free). The harvested bricks.
Genuinely-unformalized elementary group theory we *did* prove:
- `Adjacent/PrimeMul.lean` — no simple group of order `p·q`; the order-pq
  dichotomy `IsCyclic ∨ p ∣ q−1`. Pure Sylow counting. **Axiom-clean.**
- `SmallOrders.lean` — prime-power case (`p^k`, k≥2 ⟹ not simple, via p-group
  center) + the `|G|=6` concrete case.
- `PSLIwasawa.lean` — the reduction `Iwasawa ⟹ IsSimpleGroup (PSL 2 q)`
  (sorry-free reduction; the inputs are axioms in bucket B).
- `ProofStrategy.lean` `feitThompson_dichotomy` — **discharged from axiom to
  theorem 2026-05-31.** Simple group ⇒ prime-cyclic OR has an involution, proved
  on top of `Feit_Thompson_odd_order` (deep, stays axiom) + mathlib
  (`comm_iff_isSolvable`, `isCyclic`, `prime_card`, `mulEquivOfPrimeCardEq`,
  Cauchy). `#print axioms` → depends only on `Feit_Thompson_odd_order` + the 3
  standard axioms. Plus the existing assembly `classification_via_program`
  (real case-analysis proof on the milestone interfaces).
- `Wielandt.lean` `IsSubnormal.sup_normal` (warm-up), the §1 *assembly* theorems
  in `FeitThompson/BGsection1.lean` (they're proven *given* their bucket-B
  axioms), the component/layer centralizer reformulations.

### 🟦 B — STAYS AN AXIOM (deep + formalized in Coq, or genuinely deep). ~43 axioms (45 total in tree).
**Do not touch. Not targets.** These are honest dependency declarations for
results that are either (i) formalized in MathComp/Coq (the entire §1
Bender–Glauberman + Feit–Thompson line — re-porting is explicitly off the table)
or (ii) deep theory far beyond an elementary brick. Leave as `axiom`.
- **CFSG milestones** (`ProofStrategy.lean`, 8): `Burnside_paqb`,
  `Feit_Thompson_odd_order`, `aschbacher_dichotomy`,
  `oddType_isClassified`, `evenType_dichotomy`, `componentType_isClassified`,
  `quasithin_isClassified`, `nonQuasithin_char2_isClassified`.
  (`feitThompson_dichotomy` was discharged to a **theorem** 2026-05-31 — see
  bucket A — on top of `Feit_Thompson_odd_order`, which stays an axiom.)
- **CFSG itself** (`Classification.lean`, 1): `CFSG`.
- **Bender–Glauberman §1** (`FeitThompson/BGsection1/*`, ~10): `commutator_lt_of_minnormal`,
  `comm_norm_cent_subset_cent`, `critical_subgroup_exists`, `coprimeR_cent_prod`,
  `coprime_trivg_cent_Fitting_cyclic`, `cent_Fitting_le_chief_stab_of_in_Fitting`,
  `chief_stab_sub_Fitting`, `stable_factor_cent_chain'`, `coprime_cent_Phi_chain`,
  `nontrivial_assembly`, `corollary_assembly`. **All formalized in `BGsection1.v`.**
- **Family simplicity** (deep): Lie type `PSL/PSU/PSp/POmega` (`LieType.lean`, 4);
  exceptional `G2/F4/E6/E7/E8/Suzuki/SmallRee/LargeRee/3D4/2E6` (`Exceptional.lean`, 10);
  sporadic `Co1/Co2/Co3` (`Sporadics.lean`, 3).
- **Bender cornerstone — FULLY AXIOM-FREE, 2026-06-02 (`890f1f4`).**
  `genFittingSubgroup_self_centralizing` (`C_G(F*(G)) ≤ F*(G)`) is a machine-checked theorem:
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`, **no custom axioms**. Proved by
  strong induction on `|G|` (`bender_aux`) on the monotonicity bricks
  `genFittingSubgroup_map_subtype_le` (`F*(N) ≤ F*(G)`); central base case via
  `layer_eq_bot_of_le_center` then the solvability machine below. The whole F*/Bender trail
  (`GeneralizedFitting`, `LayerQuotient`, `PerfectCentralExtension`, `SolubleFittingKernel`,
  `Subnormal`) has **zero axioms**.
  ⚠️ **SOUNDNESS NOTE (2026-06-02):** commit `8042ae5` had *weakened* the kernel axiom's
  hypothesis from `layer G = ⊥` to "all minimal normals abelian", which is **false** —
  `SL(2,𝔽₅)` is a counterexample (its only minimal normal is the central `ℤ/2`, abelian, and
  `F(G)=Z(G)`, yet `F(G)≠⊤`; `SL(2,5)` is a component of itself so `layer≠⊥`). Aristotle job
  `17c03da4` found this; fixed in `3d381ed`. The discharge chain, all machine-checked:
  `fittingSubgroup_eq_top_of_isSolvable_of_le_center` (solvable Fitting kernel, ported from
  Aristotle), `fittingSubgroup_quotient_center_eq_bot` (`F(G)≤Z(G) → F(G/Z(G))=⊥`), the
  solvability induction `isSolvable_aux`, **Grün's lemma** `center_quotient_center_eq_bot_of_perfect`
  (three subgroups lemma), `perfect_central_ext_quasisimple` (ported), the subnormal-pullback
  bricks (`IsSubnormal.comap_top`, `IsSubnormal.of_characteristic_subgroupOf`), and the assembly
  `layer_quotient_center_eq_bot` (a central quotient of a component-free group is
  component-free).
  The Wielandt full join `IsSubnormal.sup` axiom was **deleted** (`7d2dc13`).
  The **component-commuting cluster is fully axiom-free**. The in-repo layer-structure lemma
  `center_eq_top_of_isMinimalNormal_of_layer_eq_bot` (no components ⟹ minimal normals abelian,
  `MinimalNormal.lean`) is a true corollary but cannot *replace* the `layer=⊥` hypothesis.
  - **Component-commuting theory: AXIOM-FREE as of 2026-06-02 (`0009c90` →
    `19c57e2`).** The arc: started as the `commute_of_ne` axiom → sharpened to
    `normalizes_of_ne` → sharpened to the *normal base case* `aschbacher_base` (with
    the subnormal-length induction proven) → **fully discharged.** The base case
    turned out NOT to need the Wielandt join: `AschbacherDichotomy.lean` proves
    `IsComponent.subnormal_dichotomy` (Aschbacher 31.4) via a *forward* induction
    along `H`'s subnormal chain (`centralizing_by_subnormal`: at each step `M ◁ J`,
    `⁅L, H⊓J⁆ ≤ H⊓M`, propagated by three-subgroups + perfectness), replacing the
    classical normal-closure `⟨L^H⟩` argument. From it, **both** `commute_of_ne`
    (exclude `L≤M` via `eq_of_le`) and `layer_commutator_fittingSubgroup_eq_bot`
    (exclude `L≤F(G)` via nilpotency) are theorems on the standard trio only. The
    proof was found by **Aristotle** (project `adf60350`, kernel-verified on a
    self-contained statement) and ported here; original in
    `aristotle-solution-components-commute.lean`, details in
    `ARISTOTLE-JOB-components-commute.md`. **The repo's belief that this needed
    `IsSubnormal.sup` was wrong** — a real lesson: a "needs the deep machinery"
    label is a hypothesis, not a fact. Net axiom change this session: −2 in this
    cluster (both `commute` and `layer_commutator` axioms gone).

### 🟥 C — PIN-LAG (already in mathlib, newer). Delete on bump. **NEVER build.**
Formalized in mathlib past our v4.29.1 pin. Building our own proof = re-deriving
what mathlib has = forbidden.
- `Alternating.lean` — general `A_n` simplicity (mathlib PR #36524, 2026-04-28,
  `alternatingGroup.isSimpleGroup`). Currently scaffolded with 3 case-witness
  **axioms** (`case{1,2,4}_*_witness`). On a host-side `lake update` past #36524:
  collapse `alternatingGroup_isSimple` to the one-liner and delete the leaves.
  ⚠️ **Cleanup candidate:** the ~250 lines of hand-built Galois case-analysis in
  this file were themselves effort re-deriving a mathlib result. Consistent with
  the one rule, this could be collapsed *now* to a single honest axiom (or the
  pending one-liner), rather than preserved. Decision pending — flagged, not done.

### 🟨 D — REAL WORK (novel + tractable + unformalized). The actual to-do.
Part of the scaffold, absent from mathlib, and provable with reasonable effort.
- **✅ CLOSED `SmallOrders.lean` `prime_card_of_simpleGroup_card_lt_sixty`** —
  "Simple, order < 60 ⟹ prime order" (≡ A_5 is the smallest non-abelian simple
  group). Verified absent from mathlib (only `IsSimpleGroup.prime_card` for
  `CommGroup`). Order-by-order Sylow grind over the mixed orders
  12,18,20,24,28,30,36,40,42,44,45,48,50,52,54,56. **Closed sorry-free in
  `22aa823` (2026-06-01), merged to main.** Trail: `propext/Classical.choice/
  Quot.sound` **+ `native_decide` trust axioms** (a few order cases, e.g.
  order-30, use `native_decide` — sorry-free but trusts the compiler, one notch
  below pure `decide`).
- **Bucket D is now EMPTY.** No known novel+tractable+unformalized brick is
  open. The next one only appears when the scaffold (bucket A) grows enough to
  expose it — so growing the architecture is the prerequisite, not a parallel
  track.

## Two debts, and the order-pin (definitional debt)

The scaffold carries two distinct kinds of debt — keep them separate:
- **Proof debt** — unproven implications. Paid by **bucket-B axioms**. Honest,
  attributed, deep.
- **Definitional debt** — `opaque` carriers (undefined objects: the 26 sporadics,
  the un-constructed Lie-type/exceptional families). The carrier exists in name
  only; nothing is asserted about its elements.

The **order-pin** chips at *definitional* debt without de-opaquing. `IsClassified.
sporadic` asserts `Nat.card carrier = order`, anchoring each opaque sporadic to its
ATLAS order. **This is cheap and safe ONLY for opaque carriers**: a wrong order is
merely *unfaithful* (the named object isn't the real group), never *contradictory*.

⚠️ **Do NOT extend the order-pin to the Lie-type families.** `PSL`/`PSp` in
`LieType.lean` are *real mathlib types*, so `Nat.card = order` asserts "my formula =
the true cardinality" — a wrong formula **contradicts reality** and makes CFSG
unprovable for genuine instances. The sporadic pin works precisely because it sits
in the sweet spot (opaque carrier + high-confidence constant), not as a general
pattern. (`PSU`/`POmega` are opaque, so a pin there would be *safe* but low-value —
the constants are less certain than the sporadics'.)

**Subtlety — the `IsClassified` Lie-type disjuncts are SAFE to pin, but deferred
on faithfulness grounds.** `Classification.lean`'s `classicalLieType` /
`exceptionalLieType` disjuncts quantify over `classicalLieTypeCarrier fam n q` /
`exceptionalLieTypeCarrier fam k`, which are **opaque** — *not* the real `PSL`/`PSp`
of `LieType.lean`. So pinning *their* order sits in the safe sweet spot (the hazard
above is specifically about the real mathlib-typed carriers). The reason it is still
**not done**: the order formulas `|PSL_n(q)|`, `|PSU_n(q)|`, `|PSp_{2n}(q)|`, `|PΩ|`,
`|G₂(q)|`, … are *parameterized* and high-confabulation-risk to reconstruct from
memory in the box (a transposed exponent is undetectable without web/ATLAS). Per
`faithfulness-not-fluency`, those are exactly the claims to *not* fluently invent.
Deferred to a web-capable session with the formulas in hand — tracked as a sibling
of `RFI-ATLAS-sporadic-orders.md`.

The ATLAS orders themselves are **documented guesses** (~85–95% confidence,
reconstructed from memory, no web in the box). The honest discipline: factored form
+ confidence-tagged docstring + `RFI-ATLAS-sporadic-orders.md` requesting an external
host/web cross-check. The internal consistency nets added on top — all `decide`-checked
in `Sporadics.lean` — raise confidence without replacing the external check:
- `order_injective` — the 26 orders are pairwise distinct (catches collision typos).
- Mathieu transitivity: `|M₁₂|=12|M₁₁|`, `|M₂₃|=23|M₂₂|`, `|M₂₄|=24|M₂₃|`.
- `happyFamily_order_dvd_monster` — all 20 Happy-Family orders divide `|M|` (tests
  the Monster's largest/least-certain value against 20 independent orders).
- `co1Subquotient_order_dvd_co1` — the 11 `Co₁` subquotients' orders divide `|Co₁|`
  (tests the second-largest uncertain value). After this, marginal value drops.

## Where the novel value actually is

Two places, and only two:
1. **Scaffold architecture (ongoing).** Stating more of CFSG's structure and
   wiring proven reductions on top of bucket-B axioms. This is unbounded,
   genuinely novel (CFSG isn't formalized anywhere), and the heart of the project.
2. **Bucket D bricks (small, finite).** Elementary results mathlib lacks and that
   aren't deep-Coq territory. **Currently empty** — `lt60` landed (2026-06-01).
   The next brick only appears once the scaffold (A) grows enough to expose it.

That bucket D is small is **correct for a scaffold**, not a failure: a well-built
scaffold is mostly architecture (A) + honest axioms (B), with a thin frontier of
hand-provable bricks (D). The mistake to avoid is mistaking a B (deep, leave it)
or a C (pin-lag, delete it) for a D (brick, build it). This map exists to prevent
exactly that.

## Counts (2026-06-02, compiler-verified)
- Top-level `axiom` declarations in the tree: **34** (`rg -c '^axiom ' FiniteSimpleGroups/`).
  This session removed **two** from the component-commuting cluster —
  `layer_commutator_fittingSubgroup_eq_bot` and (finally) the base case
  `aschbacher_base` — leaving `ComponentCommute.lean` axiom-free. ⚠️ The earlier
  headline "**44**" counted ~9 Bender–Glauberman §1 axioms under
  `FeitThompson/BGsection1/*` — **that directory is not present in this tree**, so
  either it was aspirational or those files live elsewhere; treat 34 as the verified
  current number and recount the buckets.
- `#print axioms CFSG` (the meaningful trail, unchanged this session): the **7
  milestone axioms** (`Feit_Thompson_odd_order`, `aschbacher_dichotomy`,
  `oddType_isClassified`, `evenType_dichotomy`, `componentType_isClassified`,
  `quasithin_isClassified`, `nonQuasithin_char2_isClassified`) + the standard trio.
  The local-theory axiom `aschbacher_base` is NOT in this trail (it builds toward
  Bender's cornerstone, a separate track CFSG doesn't route through).
- Real sorries: **0** — `lt60` closed in `22aa823` (2026-06-01, merged to main),
  so bucket D is empty. Repo-wide `grep "sorry"` returns only docstring prose
  (Wielandt/GeneralizedFitting/PSLIwasawa/Sporadics), no `sorry` tactic;
  `#print axioms prime_card_of_simpleGroup_card_lt_sixty` shows no `sorryAx`.
  (Was **1** at the 2026-05-31 count.)
- Build green (8284 jobs).

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
- `Wielandt.lean` `IsSubnormal.sup_normal` (warm-up), the §1 *assembly* theorems
  in `FeitThompson/BGsection1.lean` (they're proven *given* their bucket-B
  axioms), the component/layer centralizer reformulations.

### 🟦 B — STAYS AN AXIOM (deep + formalized in Coq, or genuinely deep). 40 axioms.
**Do not touch. Not targets.** These are honest dependency declarations for
results that are either (i) formalized in MathComp/Coq (the entire §1
Bender–Glauberman + Feit–Thompson line — re-porting is explicitly off the table)
or (ii) deep theory far beyond an elementary brick. Leave as `axiom`.
- **CFSG milestones** (`ProofStrategy.lean`, 9): `Burnside_paqb`,
  `Feit_Thompson_odd_order`, `feitThompson_dichotomy`, `aschbacher_dichotomy`,
  `oddType_isClassified`, `evenType_dichotomy`, `componentType_isClassified`,
  `quasithin_isClassified`, `nonQuasithin_char2_isClassified`.
- **CFSG itself** (`Classification.lean`, 1): `CFSG`.
- **Bender–Glauberman §1** (`FeitThompson/BGsection1/*`, ~10): `commutator_lt_of_minnormal`,
  `comm_norm_cent_subset_cent`, `critical_subgroup_exists`, `coprimeR_cent_prod`,
  `coprime_trivg_cent_Fitting_cyclic`, `cent_Fitting_le_chief_stab_of_in_Fitting`,
  `chief_stab_sub_Fitting`, `stable_factor_cent_chain'`, `coprime_cent_Phi_chain`,
  `nontrivial_assembly`, `corollary_assembly`. **All formalized in `BGsection1.v`.**
- **Family simplicity** (deep): Lie type `PSL/PSU/PSp/POmega` (`LieType.lean`, 4);
  exceptional `G2/F4/E6/E7/E8/Suzuki/SmallRee/LargeRee/3D4/2E6` (`Exceptional.lean`, 10);
  sporadic `Co1/Co2/Co3` (`Sporadics.lean`, 3).
- **Bender cornerstone + local theory**: `genFittingSubgroup_self_centralizing`
  (`GeneralizedFitting.lean`), the Wielandt full join `IsSubnormal.sup`
  (`Wielandt.lean`), `IsComponent.commute_of_ne` +
  `layer_commutator_fittingSubgroup_eq_bot` (`ComponentCommute.lean`, blocked on
  the Wielandt join).

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
- **`SmallOrders.lean:104` `prime_card_of_simpleGroup_card_lt_sixty`** — the one
  remaining real `sorry` in the repo. "Simple, order < 60 ⟹ prime order"
  (≡ A_5 is the smallest non-abelian simple group). Verified absent from mathlib
  (only `IsSimpleGroup.prime_card` for `CommGroup`). Order-by-order Sylow grind
  over the mixed orders 12,18,20,24,28,30,36,40,42,44,45,48,50,52,54,56.
  **In progress: delegated to Aristotle (job `lt60`).**

## Where the novel value actually is

Two places, and only two:
1. **Scaffold architecture (ongoing).** Stating more of CFSG's structure and
   wiring proven reductions on top of bucket-B axioms. This is unbounded,
   genuinely novel (CFSG isn't formalized anywhere), and the heart of the project.
2. **Bucket D bricks (small, finite).** Elementary results mathlib lacks and that
   aren't deep-Coq territory. Currently: just `lt60`. When it lands, bucket D is
   empty until the scaffold grows enough to expose another.

That bucket D is small is **correct for a scaffold**, not a failure: a well-built
scaffold is mostly architecture (A) + honest axioms (B), with a thin frontier of
hand-provable bricks (D). The mistake to avoid is mistaking a B (deep, leave it)
or a C (pin-lag, delete it) for a D (brick, build it). This map exists to prevent
exactly that.

## Counts (2026-05-31, HEAD `4dd3756`)
- Axioms: **40** (all bucket B). Real sorries: **1** (`SmallOrders`, bucket D, in
  progress). Build green (8282 jobs).

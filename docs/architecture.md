# CFSG: the architecture of the proof 🗺️

A map of the Classification of the Finite Simple Groups — the theorem, the
shape of its proof, and how this repo's scaffold lines up against it.

Primary source for the narrative: Ronald Solomon, *A Brief History of the
Classification of the Finite Simple Groups*, Bulletin AMS **38** (2001),
315–352 (open access) and Aschbacher, *The Status of the Classification of the
Finite Simple Groups*, Notices AMS **51**:7 (2004). Local copies:
`~/personal/data/cfsg/`.

The full second-generation write-up is Gorenstein–Lyons–Solomon (GLS),
*The Classification of the Finite Simple Groups*, AMS Surveys & Monographs 40,
Numbers 1–10 (1994–2023), ~5,000 pp. planned across ~12 volumes. (Paywalled;
not in Cornell alumni e-access.)

---

## The theorem

Every finite simple group `G` is isomorphic to one of:

| Family | Count | Repo carrier (`FiniteSimpleGroups/…`) |
|---|---|---|
| Cyclic `ℤ/pℤ` | ∞ (1 / prime) | ✅ real (`ZMod p`) — `Cyclic.lean` |
| Alternating `Aₙ`, `n ≥ 5` | ∞ | ✅ real (`alternatingGroup`) — `Alternating.lean` |
| Classical Lie type (`PSL, PSU, PSp, PΩᵉ`) | ∞ (16 families) | ⚖️ PSL/PSp real, PSU/PΩ opaque — `LieType.lean` |
| Exceptional Lie type (`G₂,F₄,E₆,E₇,E₈` + twisted) | ∞ | 🔴 opaque — `Exceptional.lean` |
| Sporadic (Mathieu, Janko, Conway, Fischer, Monster…) | **26** | 🔴 opaque — `Sporadics.lean` |

Stated in `Classification.lean` as the five-way disjunction `IsClassified` plus
`axiom CFSG`.

---

## The proof: one trunk, a branching analysis

Mapped onto `ProofStrategy.lean`, whose milestones now **assemble into a real
proof** (`classification_via_program`) — the leaves are axioms, the logic is
machine-checked.

### Trunk — reduce to involution centralizers
1. **Burnside `pᵃqᵇ` (1904)** — character theory's first structural win.
   `axiom Burnside_paqb`.
2. **Feit–Thompson (1962)** — *odd order ⇒ solvable*. So a nonabelian simple
   group has even order, hence (Cauchy) an **involution** `z`; study `C_G(z)`.
   255 pages; Coq-formalized 2013 (~150k lines). `axiom Feit_Thompson_odd_order`
   + the dichotomy corollary `feitThompson_dichotomy`.
3. **Brauer–Fowler (1955)** — *finitely many* simple groups share a given
   involution centralizer. Makes the enumeration finite in principle.

### The dichotomy (Gorenstein's organizing idea)
4. Every simple `G` with an involution is **odd type** or **even type**
   (≈ characteristic-2 type). The split: do involution centralizers look like
   those in a Lie group over an *odd* field (involutions semisimple, in a
   torus) or over characteristic 2? `axiom aschbacher_dichotomy`.

### Branch A — odd type (Gorenstein Steps I–VIII) → GLS program
5. **B-Theorem** (settled 1979): `L₂′(C_G(z)) = E(C_G(z))` — the centralizer
   core is a product of **quasisimple** components.
6. **Component Theorem** (Aschbacher 1973): a single *standard* component.
7. **Standard-form problems**: for each quasisimple `K`, find all `G` with `K`
   standard → Lie type over odd fields (Aschbacher [A4], Cole Prize) + some
   sporadics. Powered by the **Signalizer Functor Theorem** (Gorenstein–Walter
   → Goldschmidt → Glauberman 1973) and the generalized Fitting subgroup
   `F*(G)`. `axiom oddType_isClassified`.

### Branch B — even / characteristic-2 type (Steps IX–XVI)
8. **Thin** (`e(G)=1`): Aschbacher 1975.
9. **Quasithin** (`e(G)=2`): Mason's flawed 800-pager → **Aschbacher–Smith
   2004**, ~1200 pp. — *the last brick* (why CFSG's completion date is 2004).
   `axiom quasithin_isClassified`.
10. **`e(G) ≥ 3`**: the **Gorenstein–Lyons Trichotomy Theorem** (structural
    capstone, Steps XI/XV) → (1) char-`p` standard component (Gilman–Griess,
    Step XVI), (2) uniqueness subgroup (Aschbacher, Step X), (3) `GF(2)`-type
    (Timmesfeld/Smith — 16 sporadics live here). Tooling: BN-pairs/buildings
    (Tits, Fong–Seitz), pushing-up, the `C(G,T)`-theorem, the amalgam method
    (Goldschmidt–Stellmacher). `axiom nonQuasithin_char2_isClassified`.

Existence/uniqueness of the sporadics sits off to the side: Griess's 1980
bare-hands Monster construction (196,883-dim algebra), Sims's computer
constructions.

---

## The unifying lens: `F*(G)` (Solomon p. 343)

Don't read the big theorems as facts about simple groups — read them as
**local criteria for the generalized Fitting subgroup** `F*(G) = E(G)·F(G)`:

* B-Theorem ⟹ `F(G) = 1`, so `F*(G) = E(G)` (product of simple groups);
* Component Theorem ⟹ `F*(G)` is a *single* simple group;
* CFSG ⟹ classify all `G` with `F*(G)` nonabelian simple.

This is the thread the whole necklace hangs on, and unlike "the proof," `F*(G)`
is a *definable object* — which is why it's the right foundation for a Lean
side quest. See `FittingSubgroup.lean`.

---

## mathlib status (master 2026-05-24) — what's closeable

| CFSG ingredient | mathlib | Verdict |
|---|---|---|
| Burnside `pᵃqᵇ` solvability | ❌ only Burnside *transfer* + orbit *lemma* | hard; needs char theory mathlib lacks — axiom stays |
| Feit–Thompson | ❌ (Coq only) | axiom stays |
| `Aₙ` simple, `n ≥ 5` | ✅ `alternatingGroup.isSimpleGroup` (2026-04-28) | **real** — branch dischargeable |
| Iwasawa criterion | ✅ `MulAction.IwasawaStructure.isSimpleGroup` | the PSL engine |
| `PSL` simple | ❌ carrier real, simplicity unproven | **PSL(2,q) via Iwasawa** — `PSLIwasawa.lean` |
| Fitting subgroup `F(G)` | ❌ absent (all "Fitting" = Lie/module) | **greenfield, tractable** — `FittingSubgroup.lean` |
| `F*(G)`, `E(G)`, quasisimple, components | ❌ absent | greenfield, builds on `F(G)` |

---

## Active roadmaps in this repo

### `FittingSubgroup.lean` — `F(G)`
* ✅ `fittingSubgroup` defined (join of normal nilpotent subgroups).
* ✅ `normal_nilpotent_le_fittingSubgroup` (universal property).
* ✅ `center_le_fittingSubgroup` (center ⊆ F(G)) — first real fact.
* ⏳ `fittingSubgroup_isNilpotent` (**Fitting's Theorem**) — cited axiom;
  next step is the lemma "product of two normal nilpotent subgroups is
  nilpotent" (Isaacs Thm 9.8), then `F*(G) = E(G)·F(G)`.

### `PSLIwasawa.lean` — `PSL(2,q)` simple
* ✅ `PSL2_isSimpleGroup_of_iwasawa` — sorry-free reduction of PSL simplicity
  to the five Iwasawa obligations.
* ⏳ Construct the `ℙ¹(F_q)` action + verify nontrivial / perfect /
  quasi-preprimitive / faithful / Iwasawa-structure (see file's roadmap table).

### `ProofStrategy.lean` — the spine
* ✅ `classification_via_program` — CFSG assembled from milestone axioms by
  real case analysis. Tightened the old `: True` placeholders into typed
  milestone interfaces concluding `IsClassified`.

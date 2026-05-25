# Finite Simple Groups — Lean scaffold 🧩

A *learning scaffold* for the **Classification of Finite Simple Groups (CFSG)**.

Goal: understand the shape of the theorem and the reason "the enormous theorem" took 50 years and ~10,000 pages. Not aimed at formalization; almost everything is `sorry`. The Lean files make the structure tangible; this README does the explaining.

Bootstrapped 2026-05-25 as a side-trail in [Trevor's Lean journey](../../personal/claude/knowledge/core/projects/lean-journey/README.md).

---

## The punchline

> **Theorem (CFSG, 1955-2004).** Every finite simple group is isomorphic to exactly one of:
> 1. A **cyclic** group $\mathbb{Z}/p\mathbb{Z}$ for some prime $p$,
> 2. An **alternating** group $A_n$ for some $n \geq 5$,
> 3. A **classical group of Lie type** — one of four infinite families: $\text{PSL}_n(\mathbb{F}_q)$, $\text{PSU}_n(\mathbb{F}_q)$, $\text{PSp}_{2n}(\mathbb{F}_q)$, $\text{P}\Omega^\varepsilon_n(\mathbb{F}_q)$,
> 4. An **exceptional group of Lie type** — five untwisted ($G_2, F_4, E_6, E_7, E_8$) plus five twisted (Suzuki, Ree, Steinberg), all parametrized by a finite field,
> 5. One of **26 sporadic groups**.

Modulo small-case exceptions (e.g. $\text{PSL}_2(2) \cong S_3$ isn't simple), this is exhaustive. Every finite simple group not on this list does not exist.

---

## Why it took 50 years and 10,000 pages

**It's a confluence of independent breakthroughs**, not a single proof.

- **1832** — Galois introduces the *simplicity of $A_n$ for $n \geq 5$*, which gives the unsolvability of the quintic.
- **1861-73** — Émile Mathieu constructs $M_{11}, M_{12}, M_{22}, M_{23}, M_{24}$. First sporadic groups. *No one finds another sporadic for 92 years.*
- **1901** — Dickson constructs $G_2$ over $\mathbb{F}_q$. First "non-classical" Lie-type family.
- **1955** — Chevalley publishes *Sur certains groupes simples*, constructing $G_2, F_4, E_6, E_7, E_8$ uniformly over any field. The Lie-type families lock in.
- **1960-1961** — Suzuki and Ree find the *twisted* exceptional families. These exist only for odd powers of small primes ($2^{2n+1}$, $3^{2n+1}$) — they look sporadic but they're systematic.
- **1962** — Feit & Thompson prove the **Odd Order Theorem**: every finite simple group has even order (except the cyclic primes). 255 pages in a single issue of the *Pacific Journal*. This is the entry to CFSG: it lets you restrict attention to groups with involutions (elements of order 2).
- **1965-1976** — The **sporadic explosion**. Janko (1965, $J_1$ — first new sporadic since 1873), then 20 more sporadics over 15 years. By 1976 everyone thinks the list is essentially complete.
- **1980** — Griess constructs the **Monster** ($\sim 8 \times 10^{53}$ elements). The list closes at 26 sporadics.
- **~2004** — The classification is announced complete after Aschbacher-Smith fill the last gap (the *quasithin* case).
- **2008-present** — The *second-generation* GLS (Gorenstein-Lyons-Solomon) proof rewrites the whole thing in 12 planned volumes. 10 published by 2023.

The proof isn't one document. It's an *industry*. Hundreds of papers. ~100 authors. Bits of it (notably the original Feit-Thompson and the proof for Janko's $J_4$) are notoriously hard to read.

---

## The proof strategy at a sketch level

Given a finite simple group $G$ with an involution (Feit-Thompson handles the no-involution case):

1. Pick an involution $z \in G$. Look at its **centralizer** $C_G(z)$.
2. The structure of $C_G(z)$ tells you a lot about $G$. Classify $G$ by the structure of $C_G(z)$.
3. **Aschbacher's division**: $G$ is either of *odd type* (centralizers behave like odd-dimensional Lie groups) or *even type* (centralizers behave like even-dimensional Lie groups).
4. **Odd type** → the GLS program: $G$ is Lie-type of odd characteristic or one of a small list of sporadics.
5. **Even type** → further split by *component type* vs *characteristic 2 type*.
6. **Characteristic 2 type, quasithin** — the hard last case, finished by Aschbacher-Smith in two thick volumes (~1200 pages).

The *quasithin* case is the one that almost took CFSG down — Mason had announced it in the early 80s but his proof was found incomplete; Aschbacher-Smith redid it from scratch in the 90s-2000s.

This scaffold's `FiniteSimpleGroups/Classification.lean` states the theorem; the proof-strategy decomposition isn't in the scaffold (would be the "heavy" option — skipped to keep this light).

---

## What's actually formalized today (mid-2026)

| Piece | System | Status |
|-------|--------|--------|
| Simplicity of $\mathbb{Z}/p\mathbb{Z}$ | mathlib | Effectively done (follows from `IsSimpleGroup` + prime cardinality). |
| Simplicity of $A_n$ for $n \geq 5$ | mathlib | `alternatingGroup` defined; `IsSimple` for `n ≥ 5` proven. |
| Mathieu groups | mathlib `cfsg` branch | Skeletal; mostly `sorry`. Construction itself is hard. |
| Classification of groups of order $pq$ | Harper-Wu (Lean, merged) | Fully proven. CFSG-adjacent miniature. |
| Feit-Thompson Odd Order Theorem | **Coq** (Gonthier et al., 2013) | The landmark formalization. Not yet ported to Lean. |
| Classical groups of Lie type ($\text{PSL}_n$, $\text{PSU}_n$, ...) | mathlib | $\text{SL}_n$, $\text{GL}_n$ defined. Projective quotients + simplicity proofs: largely missing. |
| Exceptional groups of Lie type | mathlib | Not present. |
| Sporadic group constructions (beyond Mathieu) | mathlib | Not present. |
| The Monster | anywhere | Conjectural existence proven in 1980. **Not formalized anywhere.** |

---

## What's in this scaffold

### Family modules

| File | Contents |
|------|----------|
| `FiniteSimpleGroups.lean` | Root — imports everything. |
| `FiniteSimpleGroups/Basic.lean` | `IsFSG` typeclass (bundles `Finite + Nontrivial + IsSimpleGroup`). |
| `FiniteSimpleGroups/Classification.lean` | The Big Theorem stated as a disjunction over the five families. Proof: `sorry`. |
| `FiniteSimpleGroups/Cyclic.lean` | $\mathbb{Z}/p\mathbb{Z}$ simplicity. **Real proofs** — uses mathlib's `ZMod.instIsSimpleAddGroup` and `isSimpleGroup_of_prime_card`. Provides `IsFSG (Multiplicative (ZMod p))` instance. |
| `FiniteSimpleGroups/Alternating.lean` | $A_n$ simplicity for $n \geq 5$. **Real proof for $A_5$** via mathlib's `alternatingGroup.isSimpleGroup_five`, and **real structural proof for general $n \geq 5$** modulo a single helper `exists_threeCycle_of_normal` (the Galois cycle-type case analysis, sorry — but [a real mathlib PR candidate](../../personal/claude/knowledge/core/projects/lean-journey/side-quests/finite-simple-groups.md), ~half-day work). |
| `FiniteSimpleGroups/LieType.lean` | The four classical families as `opaque` types + simplicity statements with small-case exceptions. `ClassicalFamily` inductive (4 cases, `card = 4`). All simplicity claims `sorry`. |
| `FiniteSimpleGroups/Exceptional.lean` | $G_2, F_4, E_{6,7,8}$ + 5 twisted variants as `opaque` types. `ExceptionalFamily` inductive (10 cases, `card = 10`). |
| `FiniteSimpleGroups/Sporadics.lean` | All 26 sporadics as `opaque` types, organized by discovery family. **`Sporadic.Name` inductive enumerates them all**, with `card = 26` by `decide`. Pariah / Happy Family split proven (6 + 20). |
| `FiniteSimpleGroups/ProofStrategy.lean` | States the architectural milestones: Burnside $p^aq^b$, Feit-Thompson Odd Order, Aschbacher dichotomy (odd / even type), even-type sub-split, quasithin classification. All `sorry`; rich docstrings on the architecture. |

### Adjacent classification results

| File | Contents |
|------|----------|
| `FiniteSimpleGroups/Adjacent/PrimeMul.lean` | **Real Sylow-based proof** that no group of order $p\cdot q$ (distinct primes $p < q$) is simple. The Harper-Wu structural dichotomy (cyclic vs semidirect product) is stated only (`sorry`). |
| `FiniteSimpleGroups/SmallOrders.lean` | **Real proof** that no group of prime-power order $p^k$ ($k \geq 2$) is simple (uses the $p$-group center theorem). One concrete mixed-order case (order 6) proven via `PrimeMul`. The unified "no simple group of order $< 60$ except prime" statement remains `sorry` — would require Sylow case analysis on each mixed composite order $< 60$ (12, 18, 20, 24, 28, 30, 36, 40, 42, 44, 45, 48, 50, 52, 54, 56). |

### Sorry vs axiom inventory (10 files, ~950 LOC)

This scaffold distinguishes two flavors of "unproven":

- **`axiom`** (12 total) — established in the math literature; honest dependency declaration, not a TODO. Pattern borrowed from `bounded_gaps`'s axiomatization of Bombieri-Vinogradov, MPZ, etc. These are: `Classification.CFSG`, the 4 `LieType` simplicities (PSL/PSU/PSp/POmega), and all 7 `ProofStrategy` milestones (Burnside p^aq^b, Feit-Thompson, Aschbacher dichotomy, GLS odd-type, even-type dichotomy, Aschbacher-Smith quasithin, isSimpleGroup-odd-order-prime-cyclic). All of these are real theorems with proofs in the literature; formalizing them is years-to-decades of team work.
- **`sorry`** (6 total) — real TODOs, each closeable with focused effort:
  - 4 in `Alternating.lean`: the four cases of the Galois reduction (`exists_threeCycle_of_*`). Each is a commutator computation or power calculation. Half-day to a day each.
  - 1 in `Adjacent/PrimeMul.lean`: `card_eq_prime_mul_prime_classification` — the Harper-Wu cyclic-vs-semidirect dichotomy. Needs `Schur_Zassenhaus` + semidirect product construction. ~few days.
  - 1 in `SmallOrders.lean`: `prime_card_of_simpleGroup_card_lt_sixty` — unified statement covering all orders < 60. Needs per-order Sylow case analysis on the mixed composite cases (12, 18, 20, 24, 28, 30, 36, 40, 42, 44, 45, 48, 50, 52, 54, 56). ~day.

**Real proofs that landed**: $\mathbb{Z}/p\mathbb{Z}$ simplicity, $A_5$ simplicity, **general $A_n$ simplicity** (modulo the four Galois sub-cases dispatched cleanly), no-simple-pq (Sylow), no-simple-prime-power (p-group center), no-simple-order-6, `Sporadic.Name.card = 26`, `card_pariahs = 6`, `card_happy_family = 20`, `card_classicalFamily = 4`, `card_exceptionalFamily = 10`.

---

## Future direction: PSL₂(p) (Tier 2 recon)

The natural next concrete win would be **proving `PSL₂(p)` simple for prime `p ≥ 5`** — Galois's case, the smallest infinite Lie-type family member. Mathlib already has the pieces:

- **The type:** `Matrix.ProjectiveSpecialLinearGroup` in `Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup` — `PSL(n, R)` is defined as `SL(n, R) / center`. Notation `PSL(2, ZMod p)` available via `MatrixGroups` scoped namespace.
- **The criterion:** `Iwasawa.isSimpleGroup` in `Mathlib.GroupTheory.GroupAction.Iwasawa` — given an Iwasawa structure on a perfect group, deduces simplicity.

The realistic path:

1. Show `PSL(2, ZMod p)` acts on the projective line `P¹(F_p)` (faithful, transitive).
2. Construct an Iwasawa structure for that action (the "Iwasawa decomposition" — pick a Borel-style maximal abelian subgroup, conjugates generate, etc.).
3. Show `PSL(2, ZMod p)` is perfect for `p ≥ 5` (commutator subgroup = whole group).
4. Apply `Iwasawa.isSimpleGroup`.

Estimated effort: a few focused sessions. Not attempted in this scaffold; left as Tier 2 extension. Would give the scaffold one *actually proven* classical Lie-type family member, complementing the `LieType.lean` axiomatized statements.

## Build

```bash
cd ~/src/finite_simple_groups
lake update             # fetch mathlib v4.29.1 + transitives (slow first time)
lake exe cache get      # pull prebuilt oleans (much faster than building mathlib)
lake build              # compile the scaffold itself
```

Build should succeed with `sorry` warnings on most theorems. If a mathlib
identifier (e.g., `alternatingGroup`) doesn't resolve under v4.29.1, the file
will fail with an `unknown identifier` error — fix is usually `import` path or
identifier-name drift.

---

## References

PDFs are downloaded into `papers/` (git-ignored; fetch yourself from the URLs below).

### Local PDFs (`papers/`)

| File | Pages | Source |
|------|-------|--------|
| [`aschbacher-2004-notices-ams.pdf`](papers/aschbacher-2004-notices-ams.pdf) | 5 | Aschbacher, "The Status of the Classification of the Finite Simple Groups." *Notices AMS* 51(7), 2004. **The accessible overview — start here.** [\[Padua mirror\]](https://www.math.unipd.it/~tonolo/didattica/Algebra+2/aschbacher.pdf) [\[AMS\]](https://www.ams.org/notices/200407/fea-aschbacher.pdf) |
| [`solomon-2001-bulletin-ams.pdf`](papers/solomon-2001-bulletin-ams.pdf) | 10 (of 38) | Solomon, "A Brief History of the Classification of the Finite Simple Groups." *Bull. AMS* 38(3), 2001, 315-352. AMS gates the full article; only the first 10 pages download cleanly via curl. [\[DOI\]](https://doi.org/10.1090/S0273-0979-01-00909-0) |
| [`solomon-2018-afterword-ams.pdf`](papers/solomon-2018-afterword-ams.pdf) | 1 | Solomon, afterword to the 2001 survey. *Bull. AMS* 55(4), 2018. Brief post-quasithin retrospective. |
| [`gonthier-2013-feit-thompson.pdf`](papers/gonthier-2013-feit-thompson.pdf) | 6 | Gonthier et al., "A Machine-Checked Proof of the Odd Order Theorem." ITP 2013. The Coq Feit-Thompson formalization writeup. [\[Asperti mirror\]](https://www.cs.unibo.it/~asperti/PAPERS/odd_order.pdf) [\[HAL\]](https://hal.science/hal-00816699v1) |
| [`gonthier-2014-proof-engineering.pdf`](papers/gonthier-2014-proof-engineering.pdf) | 35 | Gonthier, "Proof Engineering, from the Four Color to the Odd Order Theorem." Longer essay on the formalization architecture across both efforts. [\[MSR\]](https://www.microsoft.com/en-us/research/wp-content/uploads/2014/02/georges-gonthier.pdf) |
| [`feit-obituary-2005-notices-ams.pdf`](papers/feit-obituary-2005-notices-ams.pdf) | 8 | Scott, Solomon, Thompson, Walter Feit obituary. *Notices AMS* 52(7), 2005. Useful CFSG historical context. [\[AMS\]](https://www.ams.org/notices/200507/fea-feit.pdf) |

To re-fetch:
```bash
mkdir -p papers && cd papers
UA="Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15"
curl -fsSL -A "$UA" -o aschbacher-2004-notices-ams.pdf "https://www.math.unipd.it/~tonolo/didattica/Algebra+2/aschbacher.pdf"
curl -fsSL -A "$UA" -e "https://www.ams.org/journals/bull/2001-38-03/S0273-0979-01-00909-0/" -o solomon-2001-bulletin-ams.pdf "https://www.ams.org/journals/bull/2001-38-03/S0273-0979-01-00909-0/S0273-0979-01-00909-0.pdf"
curl -fsSL -A "$UA" -e "https://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01639-X/" -o solomon-2018-afterword-ams.pdf "https://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01639-X/S0273-0979-2018-01639-X.pdf"
curl -fsSL -A "$UA" -o gonthier-2013-feit-thompson.pdf "https://www.cs.unibo.it/~asperti/PAPERS/odd_order.pdf"
curl -fsSL -A "$UA" -o gonthier-2014-proof-engineering.pdf "https://www.microsoft.com/en-us/research/wp-content/uploads/2014/02/georges-gonthier.pdf"
curl -fsSL -A "$UA" -e "https://www.ams.org/notices/200507/" -o feit-obituary-2005-notices-ams.pdf "https://www.ams.org/notices/200507/fea-feit.pdf"
```

(AMS direct PDF URLs are Cloudflare-gated; `-e` Referer header bypasses it. HAL is Anubis-gated.)

### Books (not downloadable as free PDF)

- **Gorenstein, Lyons, Solomon** — *The Classification of the Finite Simple Groups* (12-volume series, AMS, 1994-2023). The "second-generation" self-contained proof. 10 of 12 volumes published.
- **Aschbacher, Smith** — *The Classification of Quasithin Groups* I & II (AMS, 2004). The last piece of the original CFSG proof — almost 1200 pages closing the hardest sub-case.
- **Carter** — *Simple Groups of Lie Type* (Wiley, 1972). Standard Lie-type reference.
- **Wilson** — *The Finite Simple Groups* (Springer GTM 251, 2009). Modern textbook treatment, ~300pp. The non-Aschbacher choice.

### External links

- [mathlib `cfsg` branch](https://github.com/leanprover-community/mathlib4/tree/cfsg) — current Lean state of CFSG-adjacent formalization. WIP.
- [Wikipedia: Classification of finite simple groups](https://en.wikipedia.org/wiki/Classification_of_finite_simple_groups) — surprisingly thorough.
- [nLab: classification of finite simple groups](https://ncatlab.org/nlab/show/classification+of+finite+simple+groups) — categorical perspective + monstrous moonshine pointer.

---

## Status

🟡 Scaffold built. Not currently being extended — this is "look around and learn" territory, not "make a dent."

KB pointer: [side-quest doc](../../personal/claude/knowledge/core/projects/lean-journey/side-quests/finite-simple-groups.md).

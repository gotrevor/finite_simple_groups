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

| File | Contents |
|------|----------|
| `FiniteSimpleGroups.lean` | Root — imports everything. |
| `FiniteSimpleGroups/Basic.lean` | `IsFSG` typeclass (bundles `Finite + Nontrivial + IsSimpleGroup`). |
| `FiniteSimpleGroups/Classification.lean` | The Big Theorem stated as a disjunction over the five families. Proof: `sorry`. |
| `FiniteSimpleGroups/Cyclic.lean` | $\mathbb{Z}/p\mathbb{Z}$ simplicity. Cited from mathlib (sorry, but the actual lemma is one search away). |
| `FiniteSimpleGroups/Alternating.lean` | $A_n$ simplicity for $n \geq 5$. Cited from mathlib (sorry, same). |
| `FiniteSimpleGroups/LieType.lean` | The four classical families as `opaque` types + simplicity statements with small-case exceptions. All `sorry`. |
| `FiniteSimpleGroups/Exceptional.lean` | $G_2, F_4, E_{6,7,8}$ + twisted variants as `opaque` types. All `sorry`. |
| `FiniteSimpleGroups/Sporadics.lean` | All 26 sporadics as `opaque` types, organized by discovery family (Mathieu / Janko / Conway / Fischer / Monster-orbit / pariahs / McL-Suz-HS). Rich docstrings with orders. |

About 350 LOC total. Almost everything is `sorry` or `opaque`.

---

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

- Aschbacher, ["The Status of the Classification of the Finite Simple Groups"](https://www.ams.org/notices/200407/fea-aschbacher.pdf) — *Notices AMS*, 2004. The accessible overview. **Start here.**
- Gorenstein, Lyons, Solomon — *The Classification of the Finite Simple Groups* (12-volume series, AMS, 1994-2023). The "second-generation" proof.
- Carter, *Simple Groups of Lie Type* (Wiley, 1972) — the standard Lie-type reference.
- Gonthier et al., ["A Machine-Checked Proof of the Odd Order Theorem"](https://www.cs.cmu.edu/~rwh/courses/llmocaml/papers/feit-thompson.pdf) — Coq, 2013. The Feit-Thompson formalization writeup.
- [mathlib `cfsg` branch](https://github.com/leanprover-community/mathlib4/tree/cfsg) — current Lean status. WIP.
- Wilson, *The Finite Simple Groups* (Springer GTM 251, 2009) — modern textbook treatment, ~300pp. The non-Aschbacher choice.

---

## Status

🟡 Scaffold built. Not currently being extended — this is "look around and learn" territory, not "make a dent."

KB pointer: [side-quest doc](../../personal/claude/knowledge/core/projects/lean-journey/side-quests/finite-simple-groups.md).

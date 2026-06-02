# Aristotle job (PLANNED, not yet submitted): the soluble kernel of Bender's cornerstone

**Status**: spec only — architected 2026-06-02, NOT yet submitted. Bender's cornerstone
`genFittingSubgroup_self_centralizing` was discharged to a THEOREM this lap (commit `4b58cea`)
resting on exactly one axiom, the soluble kernel below. This is its planned Aristotle attack.

## The target axiom
`FiniteSimpleGroups/GeneralizedFitting.lean`:
```lean
axiom fittingSubgroup_eq_top_of_layer_eq_bot_of_le_center (G : Type*) [Group G] [Finite G]
    (hE : layer G = ⊥) (hF : fittingSubgroup G ≤ Subgroup.center G) :
    fittingSubgroup G = ⊤
```
Mathematically: a finite group with **no components** (`E(G)=1`) and **central Fitting
subgroup** (`F(G) ≤ Z(G)`, hence `F(G)=Z(G)`) equals its Fitting subgroup — i.e. it is
nilpotent (use `fittingSubgroup_eq_top_iff_isNilpotent`, proved this lap). This is the
soluble-type `C_G(F(G)) ≤ F(G)`, central + component-free case (Aschbacher 31.13;
Kurzweil-Stellmacher 6.5.8). The `E(G)=1` hypothesis is essential — `A₅` is the counterexample
without it (`F(A₅)=1≤Z`, `F(A₅)≠⊤`), excluded because `A₅` is its own component.

## Why it is hard / the decomposition
Two genuinely separate pieces:
- **(a) structure:** `layer G = ⊥ ⟹ every minimal normal subgroup of G is abelian.` A
  non-abelian minimal normal subgroup is a direct product of isomorphic non-abelian simple
  groups, each of which is a subnormal quasisimple subgroup = a **component**, contradicting
  `layer = ⊥`. Needs the char-simple = product-of-simples decomposition (NOT in mathlib/repo
  in usable form — itself a real sub-project).
- **(b) soluble climb:** with all minimal normals abelian and `F(G)` central, derive `F(G)=G`.

## Recommended submission strategy (self-contained, mirror the components-commute job)
Two viable framings — prefer the first:
1. **Hand Aristotle (b) only, in pure mathlib terms.** State: *for finite `G`, if `F(G)` (the
   sSup of normal nilpotent subgroups, inlined) is central and every minimal normal subgroup of
   `G` is abelian, then `F(G) = ⊤`.* Provide the inline `fittingSubgroup` def matching the repo
   (`sSup {H | H.Normal ∧ Group.IsNilpotent H}`). This is the genuinely soluble part; if Aristotle
   solves it, (a) becomes a separate, sharper in-repo/Aristotle target (a clean
   layer-structure lemma).
2. **Hand the whole kernel**, inlining `fittingSubgroup`, `layer`, `IsComponent`, `IsQuasisimple`,
   `IsSubnormal`, `IsNormalStep`, `center`, **plus a usable inline axiom** supplying (a)
   (`layer = ⊥ → every min normal abelian`), so Aristotle does only the climb. Larger file, but
   one job. (This mirrors how the components-commute job supplied the Wielandt join as a usable
   axiom and Aristotle then didn't even need it.)

## Mechanics (from ARISTOTLE-JOB-components-commute.md, verified this fleet)
- CLI at `/usr/local/bin/aristotle`. `aristotle submit <prompt> --project-dir <dir>` (async; do
  NOT `--wait`). `aristotle list` to poll status. `aristotle download <uuid> --destination ...`.
- Build a `/tmp/aristotle-bender/Target.lean`: `import Mathlib`, inline the minimal defs above
  **byte-faithful to the repo** (so the proof ports), goal theorem = the only `sorry`.
- **On return: verify in OUR kernel before trusting** — compile in v4.29.1, check
  `#print axioms <thm>` is `[propext, Classical.choice, Quot.sound]` (+ any usable axiom you
  supplied), no `sorryAx`, and that the inlined statement is identical to the repo's. Then port.
- NOTE this lap: a job was already RUNNING on the shared fleet account; submit is still fine
  (separate project) but mind concurrency.

## Port-back plan
Map inline defs → repo defs (`FittingSubgroup.lean`, `Components.lean`, `Quasisimple.lean`,
`Subnormal.lean`). If framing (1): the ported proof discharges (b); then the residual axiom is
(a) (`layer = ⊥ → min normals abelian`) — strictly sharper, purely structural. If framing (2):
the kernel axiom is fully discharged and Bender's cornerstone becomes axiom-free down to the
standard trio.

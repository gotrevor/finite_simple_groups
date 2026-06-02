# Aristotle job: the soluble kernel of Bender's cornerstone

**Status**: **SUBMITTED 2026-06-02** · **Project UUID `17c03da4-8ea8-464b-bb37-b354239569bb`**
· framing (1) (the pure soluble climb, no component defs). Awaiting result. Bender's cornerstone
`genFittingSubgroup_self_centralizing` was discharged to a THEOREM this lap (commit `4b58cea`)
resting on exactly one axiom, the soluble kernel below. This job attacks that kernel.

## TWO jobs submitted (the kernel's two halves)
- **(b) soluble climb** — project `17c03da4-8ea8-464b-bb37-b354239569bb` (`aristotle-bender`):
  `soluble_fitting_kernel` (all min normals abelian + central F(G) ⟹ F(G)=⊤). File
  `/tmp/aristotle-bender/Target.lean`.
- **(a) layer-structure** — project `be54b396-d794-4d46-8f5a-5ad9a00d2e0b` (`aristotle-minnormal`):
  `nonabelian_minNormal_has_simple_normal` (a non-abelian minimal normal subgroup has a normal,
  simple, non-abelian subgroup). File `/tmp/aristotle-minnormal/Target.lean`.

**In-repo consumers already built & green this lap** (so porting is near-`exact`):
- `layer_ne_bot_of_normal_simple_factor` (LayerNormal) consumes (a)'s output → `layer G ≠ ⊥`.
- `isComponent_of_isSubnormal_of_isSimpleGroup`, `layer_ne_bot_of_isComponent` (the components).
- `layer_eq_bot_of_le_center`, `genFittingSubgroup_map_subtype_le`, `fittingSubgroup_eq_top_iff_isNilpotent`.

## Poll / collect (next lap)
```
aristotle list                         # find 17c03da4 / be54b396 status (avoid `show` — live TUI)
aristotle download 17c03da4-8ea8-464b-bb37-b354239569bb --destination /tmp/sk.tar.gz
aristotle download be54b396-d794-4d46-8f5a-5ad9a00d2e0b --destination /tmp/mn.tar.gz
tar -xzf /tmp/sk.tar.gz -C /tmp/sk && rg -n "sorry|soluble_fitting_kernel" /tmp/sk
tar -xzf /tmp/mn.tar.gz -C /tmp/mn && rg -n "sorry|nonabelian_minNormal" /tmp/mn
```
**Independent alternative to (a):** the layer-structure fact is *elementary* (no deep theorem) —
minimal normal ⟹ characteristically simple (via `Subgroup.normal_of_characteristic_of_normal` +
minimality); a finite char-simple non-abelian group has a non-abelian minimal normal subgroup
(socle = ⊤ + distinct minimal normals commute ⟹ all-abelian would force abelian); strong
induction on `|G|` descends to a simple non-abelian subnormal subgroup. Can be done in-repo
without Aristotle if (a)'s job stalls.
Submitted file preserved at `/tmp/aristotle-bender/Target.lean` (regenerate from the git
history of this note if `/tmp` is wiped). The submitted statement (verified to elaborate in our
v4.29.1 toolchain, only the goal `sorry`):
```lean
theorem soluble_fitting_kernel (G : Type*) [Group G] [Finite G]
    (hmin : ∀ M : Subgroup G, IsMinimalNormal M → ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hF : fittingSubgroup G ≤ Subgroup.center G) : fittingSubgroup G = ⊤
```
with `fittingSubgroup` inlined byte-identical to the repo and `IsMinimalNormal M :=
M.Normal ∧ M ≠ ⊥ ∧ ∀ N, N.Normal → N ≠ ⊥ → N ≤ M → N = M`.

**If SOLVED:** verify in our kernel (`#print axioms`, no `sorryAx`, statement faithful), port the
proof into a new repo lemma `soluble_fitting_kernel`, then discharge the repo axiom
`fittingSubgroup_eq_top_of_layer_eq_bot_of_le_center` from it by supplying the missing
hypothesis — i.e. prove the residual **(a)** `layer G = ⊥ → every minimal normal subgroup of G
is abelian` (a clean structural lemma: a non-abelian minimal normal subgroup is a product of
non-abelian simple groups, each a component, contradicting `layer = ⊥`). That residual (a) is
then the sole sharper axiom (or a further Aristotle target).

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

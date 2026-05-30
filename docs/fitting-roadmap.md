# Discharging `fittingSubgroup_isNilpotent` — roadmap

Goal: replace `axiom fittingSubgroup_isNilpotent` in `FittingSubgroup.lean`
with a proof. `F(G) = sSup {H | H.Normal ∧ IsNilpotent H}`.

## The route: finite-nilpotency TFAE

`Mathlib.GroupTheory.Nilpotent.isNilpotent_of_finite_tfae` gives, for finite G:

```
IsNilpotent G ↔ ∀ p [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal
```

So `F(G)` is nilpotent **iff every Sylow of `F(G)` is normal in `F(G)`**.
mathlib has **no `pCore`/`O_p`**, so we build the decomposition by hand.

## Confirmed mathlib bricks (verified present, v4.29.1)

- `normalizerCondition_of_isNilpotent [IsNilpotent G] : NormalizerCondition G`
  (Nilpotent.lean:877)
- `Sylow.normal_of_normalizerCondition (hnc) (P : Sylow p G) : (↑P).Normal`
  (Sylow.lean:766)
- `Sylow.characteristic_of_normal (h : (↑P).Normal) : (↑P).Characteristic`
  (Sylow.lean:736)
- `ConjAct.normal_of_characteristic_of_normal {H : Subgroup G} [H.Normal]
  {K : Subgroup H} [K.Characteristic] : (K.map H.subtype).Normal`
  (ConjAct.lean:270) — an **instance**, so resolved by `infer_instance`. The
  char-in-normal ⇒ normal transport.
- `isNilpotent_of_finite_tfae` (the iff above; clause 4 ↔ clause 1)
- `Sylow.directProductOfNormal`, `isNilpotent_of_product_of_sylow_group`

## Done (branch `cfsg-fitting-nilpotent`, commit 1a4a31e)

- `sylow_characteristic_of_isNilpotent` — in a finite nilpotent group every
  Sylow is characteristic. Axiom-free, build green.
- `sylow_normal_of_normal_nilpotent` — Sylow of a normal nilpotent `N ⊴ G`
  (G finite), mapped to G, is normal in `G`. Composes brick 1 + the ConjAct
  transport instance. Axiom-free, build green.

Build check: `lake build FiniteSimpleGroups.FittingSubgroup` → EXIT 0, 8248
jobs, no sorry/warning.

## Remaining skeleton

2. **Hand-rolled p-core.** For each prime `p`, define
   `Op G p := ⨆ {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q}` (join of normal
   p-subgroups). Show it is a normal p-subgroup (join of normal p-subgroups in
   a finite group is a p-group — via order/`IsPGroup` API). The substantial
   middle.

3. **`Op G p ≤ F(G)`** (a normal p-group is nilpotent, so it's in the sSup).

4. **Every Sylow of `F(G)` is one of these normal pieces** ⇒ normal in `F(G)`.
   Then apply `isNilpotent_of_finite_tfae` clause 4 → 1. This closes
   `fittingSubgroup_isNilpotent`; `fittingSubgroup_normal` likely falls out of
   the same `Op` decomposition.

Brick 2 finishes step 1. Step 2 (the p-core) is the next real target.

## Dev loop note

Full `lake build` OOMs in low-RAM sandboxes (mmap of ~8280 prebuilt oleans).
Build the single target instead: `lake build FiniteSimpleGroups.FittingSubgroup`
(deps cached → ~6-19s). Environment limit, not a code issue.

## Verification discipline (learned this session)

Report build/commit status only from clean, re-confirmed output. The harness
intermittently replays/scrambles tool-result batches; cross-check HEAD with a
fresh `git --no-pager log` / `git rev-parse`, run git steps as single
sequential calls (not parallel batches), and never narrate a commit hash you
haven't just seen from `rev-parse`. (This session fabricated phantom hashes
twice off scrambled output before catching it.)

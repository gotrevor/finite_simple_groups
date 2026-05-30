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
- `IsPGroup.isNilpotent [Finite G] : IsPGroup p G → IsNilpotent G`
  (Nilpotent.lean:885) — finite p-group is nilpotent.
- `IsPGroup.to_sup_of_normal_right {H K} (hH : IsPGroup p H) (hK : IsPGroup p K)
  [hK.Normal] : IsPGroup p ↥(H ⊔ K)` (PGroup.lean:271), and `_left`/`'` variants.
  **Binary** sup of normal p-groups is a p-group.
- `Subgroup.sup_normal (H K) [H.Normal] [K.Normal] : (H ⊔ K).Normal`
  (Subgroup/Pointwise.lean:367) — instance.

## Done (branch `cfsg-fitting-nilpotent`)

- `sylow_characteristic_of_isNilpotent` (1a4a31e) — in a finite nilpotent group
  every Sylow is characteristic. Axiom-free, build green.
- `sylow_normal_of_normal_nilpotent` (1a4a31e) — Sylow of a normal nilpotent
  `N ⊴ G` (G finite), mapped to G, is normal in `G`. Composes brick 1 + the
  ConjAct transport instance. Axiom-free, build green.
- `normal_pgroup_le_fittingSubgroup` (5f2e9c8) — a normal p-subgroup of a finite
  group is nilpotent (`IsPGroup.isNilpotent`) hence ≤ `F(G)`. **Roadmap step 3
  done.** Axiom-free, build green.

Build check: `lake build FiniteSimpleGroups.FittingSubgroup` → EXIT 0, 8249
jobs, no sorry/warning.

## Remaining skeleton

2. **Hand-rolled p-core (the substantial middle, NEXT TARGET).** Define
   `Op G p := sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q}` and prove it is a
   normal p-subgroup. Two obligations:
   - **`(Op G p).Normal`** — sSup of normal subgroups. ⚠️ No direct
     `sSup`/`iSup`-of-normals lemma surfaced in mathlib v4.29.1 (only the binary
     `sup_normal` instance). Plan: in a finite group the index set is finite, so
     `sSup = Finset.sup`; induct with the binary `sup_normal`. (Alt: investigate
     `Subgroup.normalClosure` to get normality for free, then show it coincides.)
   - **`IsPGroup p ↥(Op G p)`** — sSup of normal p-groups is a p-group. Same
     finite-`Finset.sup` induction, stepped with `to_sup_of_normal_right` (each
     intermediate sup must be carried as *both* normal and a p-group, so the
     induction motive is the conjunction). This is the real work — a multi-lemma
     `Finset.induction` proof, budget a focused session.

3. ✅ **`Op G p ≤ F(G)`** — already covered by `normal_pgroup_le_fittingSubgroup`
   above (apply it to `Op G p` once step 2 gives normal + p-group).

4. **Every Sylow of `F(G)` is one of these normal pieces** ⇒ normal in `F(G)`.
   Then apply `isNilpotent_of_finite_tfae` clause 4 → 1. This closes
   `fittingSubgroup_isNilpotent`; `fittingSubgroup_normal` likely falls out of
   the same `Op` decomposition.

Steps 1 and 3 are done. Step 2 (the p-core normality + p-group induction) is the
next real target and the bottleneck.

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

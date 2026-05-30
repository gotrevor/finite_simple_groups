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

2. ✅ **Hand-rolled p-core — DONE.** `pCore G p := sSup {Q | Q.Normal ∧
   IsPGroup p Q}`, with:
   - `pCore_normal` (30907b3) — via `sSup_normal_of_forall_normal` (2a, which
     proves sSup-of-normals is normal; mathlib only had the `iInf` version).
   - `isPGroup_pCore` (0bb0a37) — the defining set is finite (`Finite G ⇒
     Finite (Subgroup G)`, `Set.toFinite`), so `pCore = Finset.sup id`;
     `Finset.sup_induction` with motive `(·.Normal ∧ IsPGroup p ·)` carried
     jointly, stepped by `IsPGroup.to_sup_of_normal_right` + `Subgroup.sup_normal`,
     based at `IsPGroup.of_bot`.

3. ✅ **`Op G p ≤ F(G)`** — `normal_pgroup_le_fittingSubgroup` applied to
   `pCore_normal` + `isPGroup_pCore`.

4. **Close `fittingSubgroup_isNilpotent` (THE REMAINING BOTTLENECK).** The
   classical decomposition `F(G) = ⨆_p O_p(G)`, then nilpotent because it's an
   internal direct product of the (coprime-order, normal) p-cores. Two real
   sub-goals, neither yet done:
   - **`F(G) ≤ ⨆_p O_p(G)`** (the reverse `≥` is immediate from step 3). For a
     normal nilpotent `N ⊴ G`: `N` is the join of its Sylows (nilpotent ⇒ direct
     product of Sylows, from `isNilpotent_of_finite_tfae` clause 5), and each
     Sylow of `N` is a *normal* p-subgroup of `G` — exactly brick 2
     (`sylow_normal_of_normal_nilpotent`) — hence `≤ O_p(G)`. So `N ≤ ⨆_p O_p(G)`;
     take `sSup` over all such `N`. **Brick 2 is the load-bearing piece here** —
     this is what it was built for.
   - **`⨆_p O_p(G)` is nilpotent.** The `O_p(G)` are normal with pairwise coprime
     orders ⇒ they pairwise commute and form an internal direct product ⇒ the join
     is `≃* ∏_p O_p(G)`, a finite product of (nilpotent) p-groups, hence nilpotent
     (`nilpotent_of_mulEquiv` + product-of-nilpotents). ⚠️ The internal-direct-
     product / coprime-commute plumbing is the genuinely hard, possibly multi-
     session part; mathlib's `Sylow.directProductOfNormal` is the closest analog
     and worth mining first.

   Once `F(G)` is shown nilpotent, `fittingSubgroup_normal` should fall out of the
   same `⨆_p O_p` description (join of normals).

**Steps 1, 2, 3 are DONE and verified (6 axiom-free lemmas + the `pCore` def).**
Step 4 is the remaining work to actually discharge the axiom — and it is NOT
small: the coprime internal-direct-product argument is the real mathematical
content. The axiom `fittingSubgroup_isNilpotent` is still in place.

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

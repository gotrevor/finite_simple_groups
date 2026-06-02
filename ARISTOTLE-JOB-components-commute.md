# Aristotle job: distinct components commute (⁅L,M⁆ = ⊥)

**Submitted** 2026-06-02 · **Project UUID** `adf60350-2414-40ec-8105-d9327383ff62`
· name `aristotle-normalize` · status at submit: RUNNING.

## What it's proving
The bounded core under `IsComponent.normalizes_of_ne` / `commute_of_ne`: in a
**finite** group, two distinct components `L ≠ M` satisfy `⁅L, M⁆ = ⊥`
(Aschbacher *Finite Group Theory* 31.4). Handed off because the proof is a real
chunk of local group theory (induction on subnormal length; base case
`H ⊴ G ⟹ L ≤ H ∨ ⁅L,H⁆=1`) — architected here, offloaded per the box guidance.

## Submission (self-contained, NOT the repo)
- Source: `/tmp/aristotle-normalize/Target.lean` (regenerate if `/tmp` is gone —
  the statement is reproduced below in spirit; see git history of this note).
- Inlines minimal `IsNormalStep` / `IsSubnormal` (ReflTransGen) / `IsQuasisimple`
  (perfect + simple-mod-center) / `IsComponent`, matching the repo's defs.
- **Wielandt's join is provided as an axiom `isSubnormal_sup`** (the repo already
  carries it as `IsSubnormal.sup`), so Aristotle may use it freely.
- Goal theorem `components_commute` is the only `sorry`. Self-contained so
  Aristotle wraps its own v4.28.0 mathlib (we're v4.29.1 — minor drift; the
  statement uses only stable Subgroup/commutator/normalizer/ReflTransGen API).

## How to poll / collect (any session)
```
aristotle list                              # fast; find adf60350… status (NOT `show` — that's a live TUI)
aristotle download adf60350-2414-40ec-8105-d9327383ff62 --destination /tmp/ac.tar.gz
tar -xzf /tmp/ac.tar.gz -C /tmp/ac && rg -n "sorry|theorem components_commute" /tmp/ac
```

## Integration plan if it succeeds
The proof will be against the inline self-contained defs. Port into the repo:
- Map `isSubnormal_sup` → repo `FiniteSimpleGroups.IsSubnormal.sup`.
- Map inline `IsComponent`/`IsQuasisimple`/`IsSubnormal` → repo equivalents
  (`Components.lean`, `Quasisimple.lean`, `Subnormal.lean`) — same shapes.
- Then EITHER: (a) discharge `IsComponent.commute_of_ne` directly from the ported
  proof (and **drop the `normalizes_of_ne` axiom entirely** — the deep debt
  collapses to just `IsSubnormal.sup`); or (b) if the proof naturally yields the
  normalize fact, discharge `normalizes_of_ne` and keep the existing wrapper.
- Re-run `#print axioms`: target trail = `IsSubnormal.sup` + standard trio, no
  `sorryAx`. Net win: one fewer honest axiom in the local-theory cluster.

## Fallback if it fails / times out
Leave `normalizes_of_ne` as the (sharper) axiom — `commute_of_ne` already rests on
it as a theorem (commit `0009c90`). Re-attempt later, or hand the narrower base
case (`H ⊴ G ⟹ L ≤ H ∨ ⁅L,H⁆=1`) to Aristotle instead of the full statement.

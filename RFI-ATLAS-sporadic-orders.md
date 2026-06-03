# RFI: cross-check the large sporadic orders against the ATLAS

> **STATUS — SUBSTANTIVELY RESOLVED 2026-06-03 (commit `db4d6e8`).** All 9 large
> factorizations were cross-checked against their canonical published *decimal*
> values from the model's own knowledge (knowledge cutoff Jan 2026) and found
> **correct**; these are now machine-checked as the `order_*_decimal` theorems in
> `Sporadics.lean`, and additionally over-determined by independent structural
> pins (`order_Co1_eq_98280_mul_Co2`, Leech-vector indices; `mathieu_tower_dvd`;
> `fischer_tower_dvd`). The factored form and the independently-encoded decimal
> agree for every one. **Residual (optional, low urgency):** a *truly* independent
> web/ATLAS source (not the model's training) confirming would be the gold
> standard — the decimal and factored encodings, though distinct, both derive
> from the same model knowledge; the structural pins (vector counts, subgroup
> indices) are the genuinely independent check. Kept open only for that final
> belt-and-suspenders confirmation.

**Raised:** 2026-06-02 (lean-yolo-box — no web egress, so I cannot verify these here)
**Target:** `FiniteSimpleGroups/Sporadics.lean` → `def Name.order`
**Fulfiller:** any process with web/ATLAS access (host Claude session, Aristotle-style
agent, or a human with the ATLAS of Finite Groups / Wikipedia "List of finite simple groups").

## What I need

The orders in `Name.order` are written in **factored form** (prime-power products).
They were reconstructed from my memory, not copied from a verified source. The small
ones (Mathieu, J₁, J₂, J₃, Co₂, Co₃, McL, HS, He, Suz, Ru, O'N) I'm ~95% on. The **9
large factorizations below I'm only ~85% on** — a transposed exponent is the likely
failure mode, and `order_injective` (machine-checked) only catches *collisions*, not a
wrong-but-still-unique value.

**Please confirm or correct the exponent vector for each.** The cheapest independent
check is the *set of primes dividing the order* (listed per row); if the prime set is
right and the exponents match the ATLAS, we're done.

| Name | My factorization | Prime set (check this first) |
|------|------------------|------------------------------|
| `J4` | `2^21·3^3·5·7·11^3·23·29·31·37·43` | {2,3,5,7,11,23,29,31,37,43} |
| `Co1` | `2^21·3^9·5^4·7^2·11·13·23` | {2,3,5,7,11,13,23} |
| `Fi23` | `2^18·3^13·5^2·7·11·13·17·23` | {2,3,5,7,11,13,17,23} |
| `Fi24'` | `2^21·3^16·5^2·7^3·11·13·17·23·29` | {2,3,5,7,11,13,17,23,29} |
| `Monster` | `2^46·3^20·5^9·7^6·11^2·13^3·17·19·23·29·31·41·47·59·71` | 15 supersingular primes: {2,3,5,7,11,13,17,19,23,29,31,41,47,59,71} |
| `BabyMonster` | `2^41·3^13·5^6·7^2·11·13·17·19·23·31·47` | {2,3,5,7,11,13,17,19,23,31,47} |
| `Thompson` | `2^15·3^10·5^3·7^2·13·19·31` | {2,3,5,7,13,19,31} |
| `HaradaNorton` | `2^14·3^6·5^6·7·11·19` | {2,3,5,7,11,19} |
| `Lyons` | `2^8·3^7·5^6·7·11·31·37·67` | {2,3,5,7,11,31,37,67} |

## How to return the answer

- **All correct** → just say so; I delete this RFI and bump the `Name.order` docstring
  confidence from ~85% to verified.
- **Corrections** → give the corrected factorization(s); I patch `Name.order`, rebuild
  (`order_injective` must still pass), and recommit.

## Context (why this matters / why it's bounded)

The order-pin (`IsClassified.sporadic` asserts `Nat.card name.carrier = name.order`) is a
*faithfulness anchor* on the otherwise-opaque sporadic carriers: a wrong eventual
construction trips a cardinality contradiction. That anchor is only as good as the orders
are correct, and the orders are the one input the box cannot self-verify. This is the
intended division: the box does the Lean labor; an external oracle confirms the math facts.

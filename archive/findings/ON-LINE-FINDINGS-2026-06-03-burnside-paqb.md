# Online findings — Burnside `pᵃqᵇ` character-theoretic core (answers ON-LINE-REQUEST.md 2026-06-03)

Fulfilled from a networked host session 2026-06-03. Primary sources: the live mathlib
tree this repo pins (v4.29.1, rev `5e932f97`) **and** mathlib `master`; the repo's own
`FiniteSimpleGroups/CharacterTheory.lean` + `Burnside.lean`; the live
`math-comp` GitHub source (the Coq formalization).

---

## ⚠️ TL;DR — the gap is now a SINGLE item, and the request's "(2) still missing" is stale

Reading the repo's own `CharacterTheory.lean` (its docstring + proved theorems) shows
the fleet has **already finished ingredient (2)** since "update 2" was written:

* (1) `χ(g)` algebraic integer — ✅ `Representation.character_isIntegral` (proved).
* **(2) central-character integrality `[G:C_G(g)]·χ(g)/χ(1) ∈ ℤ̄` — ✅ `classSize_char_isIntegral`
  (PROVED in-repo), via `classSum` + `classSum_isIntegral` + Schur
  (`exists_scalar_isIntegral_of_central`). The "⛔ STILL MISSING" in the request is out
  of date.**
* (4) Kronecker — ✅ mathlib `NumberField.Embeddings.pow_eq_one_of_norm_le_one`.
* (5) `-1/p ∉ ℤ̄` — ✅ `not_isIntegral_neg_inv_prime` (proved).
* (6) scalar ⟹ proper normal — ✅ structural half (`scalarSubgroup`, `scalarSubgroup_normal`,
  `comm_of_scalarSubgroup_eq_top`).
* **(3) column orthogonality `∑_χ χ(1)·χ(g) = 0` for `g ≠ 1` — ⛔ THE ONE REMAINING GAP.**

So the entire open-web question reduces to: **how to get (3), and is it anywhere to
port.** Answers below.

---

## Q1. mathlib state — verified against v4.29.1 AND master

**Master `RepresentationTheory/` is identical to v4.29.1** (only adds a `Continuous/`
subdir, irrelevant). So "bump mathlib" buys nothing here. Decl-level:

**NOT in mathlib (either version):**
* ❌ Burnside `pᵃqᵇ` itself. (`grep Burnside` hits only `GroupTheory/Transfer.lean` =
  Burnside's *normal p-complement* theorem and `GroupAction/Quotient.lean` = Burnside's
  *counting* lemma — neither is `pᵃqᵇ`. The `docs/1000.yaml` / `overview.yaml` hits are
  "wanted theorem" lists, not proofs.)
* ❌ **Column / second orthogonality.** `char_orthonormal` is strictly *row*
  orthonormality: `(|G|⁻¹) ∑_{g} χ(g)·σ(g⁻¹) = [σ ≅ ρ]`. No column relation.
* ❌ `#Irr(G) = #ConjClasses(G)`, no packaged finset `Irr(G)`, no "irreducible characters
  are a basis of the class functions." (Only `char_conj` = "χ constant on classes".)
* ❌ central characters / class sums `z_C` / `Z(ℂ[G])` machinery — **none in mathlib**
  (the repo built its own: `classSum`, `classSum_isIntegral`, `classSum_central`).
* ❌ regular-representation *character* / its decomposition with multiplicities.

**Present in mathlib (usable bricks):**
* ✅ `Representation.char_orthonormal` / `FDRep.char_orthonormal` — row orthonormality.
* ✅ `Rep.leftRegular k G` (`RepresentationTheory/Rep/Basic.lean`) — the regular rep object
  (but not its character formula or decomposition).
* ✅ Maschke (`Maschke.lean`) + semisimplicity (`Semisimple.lean`) — complete reducibility.
* ✅ `FinGroupCharZero.simple_iff_char_is_norm_one` (`⟨χ,χ⟩ = 1 ↔ V simple`) — a handy
  irreducibility test.
* ✅ Kronecker (`NumberField.Embeddings.pow_eq_one_of_norm_le_one`, the repo already wires
  this in).
* ✅ **Wedderburn–Artin — the structural backbone, and the key to (3).** mathlib HAS:
  * `IsSemisimpleRing (MonoidAlgebra k G)` / `IsSemisimpleModule k[G] V` (Maschke.lean) — so
    `ℂ[G]` is semisimple (finite `G`, `NeZero (Nat.card G : ℂ)`).
  * `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
    (`RingTheory/SimpleModule/IsAlgClosed.lean`): a finite-dimensional semisimple algebra over
    an **algebraically closed** field `≅ ∏ᵢ Matrix (Fin dᵢ) (Fin dᵢ) F`. Applied to `ℂ[G]`:
    **`ℂ[G] ≃ₐ[ℂ] ∏ᵢ Mₐᵢ(ℂ)`** — the full Artin–Wedderburn decomposition.
  This is exactly the "finite family of simple modules / `∑dᵢ²=|G|`" update-3 asks about, and
  it is **already in mathlib** — the hard infrastructure is done.

## Q2 + Q4. Existing formalizations — Coq mathcomp has the WHOLE theorem (the port blueprint)

**Coq Mathematical Components fully formalizes Burnside `pᵃqᵇ`**, following Isaacs
*Character Theory* Ch. 2–3, in **`group_representation/integral_char.v`** (verified against
live `math-comp/master`). The exact chain — this is your map, decl-for-decl:

| Isaacs | mathcomp decl (`integral_char.v` unless noted) | repo counterpart |
|---|---|---|
| 2.4 | `gring_classM_expansion` — class-sum algebra `'K_i *m 'K_j = ∑ a_ijk 'K_k` | `classSum` + `classSum_central` |
| 3.7/3.8 | `coprime_degree_support_cfcenter` — `gcd(|C|,χ(1))=1 ⟹ χ(g)=0 ∨ g∈Z(χ)` | `classSize_char_isIntegral` + the gcd/Kronecker finish (TODO) |
| **3.9** | **`primes_class_simple_gt1`** — a simple group has no class whose size has a single prime ( > 1) | **= the repo's axiom `isSimpleGroup_centralizer_index_not_primePow`** |
| **3.10** | **`Burnside_p_a_q_b : (size (primes #\|G\|) <= 2) -> solvable G`** | `Burnside.burnside_simple` / `ProofStrategy.Burnside_paqb` |
| — | `second_orthogonality_relation` (`group_representation/character.v:1281`) | **the missing (3)** |
| — | `NirrE : Nirr G = #\|classes G\|` (`character.v:556`) | the `#Irr=#classes` (3) depends on |
| 3.15 | `nonlinear_irr_vanish` — Burnside vanishing | (not needed for the `pᵃqᵇ` route) |

mathcomp's `Burnside_p_a_q_b` proof is **structurally identical to the repo's**: induct on
`|G|`; non-simple ⟹ `series_sol` on a proper normal subgroup; simple ⟹ take `p | |G|`, a
Sylow `P`, a nontrivial `g ∈ Z(P)` (so `P ≤ C_G(g)`, hence `|gᴳ| = [G:C_G(g)]` is
`p`-free ⟹ ≤ 1 prime), then `primes_class_simple_gt1` forbids that class ⟹ `G` abelian ⟹
solvable. **The repo's `burnside_aux` + the `isSimpleGroup_centralizer_index_not_primePow`
axiom is exactly this skeleton.** So the repo's architecture is validated, and mathcomp's
`integral_char.v` is the line-by-line blueprint for discharging the axiom.

* **`solvable/burnside_app.v` is a red herring** — it's Burnside's *counting* lemma applied
  to colorings of a square/cube, not the `pᵃqᵇ` theorem.
* **No Lean formalization** of Burnside `pᵃqᵇ` exists — verified beyond mathlib via a
  GitHub-wide Lean code search (covers Reservoir's population = public Lake packages;
  sanity-checked that the search finds known terms like `char_orthonormal`). The only
  "Burnside" in any Lean repo is the *counting* lemma (`GroupAction/Quotient`,
  `NeilStrickland/lean_lib/burnside_count.lean`) and the *Burnside category*
  (`robin-carlier/SymmMonCoherence`) — neither is the `pᵃqᵇ` theorem, and nothing carries
  `second_orthogonality` in Lean.
* **Isabelle AFP — correction of the in-request claim.** The request (update 3) supposes
  "Isabelle character-theory AFP entries have the second orthogonality relation." **They do
  not.** The relevant AFP entry, Sylvestre's *Representations of Finite Groups* (2015),
  formalizes Maschke, Schur, Frobenius reciprocity, and finiteness of the iso-classes of
  irreducibles — **but no characters and no orthogonality relations** (verified on the entry
  page). `Jacobson_Basic_Algebra` has no character theory either. So there is **no Isabelle
  formalization of character orthogonality** to port.
* **Net:** **Coq mathcomp is the sole existing formalization** of column/second orthogonality
  (`second_orthogonality_relation`) and of Burnside `pᵃqᵇ` (`Burnside_p_a_q_b`) — the only
  port reference. **This repo would be the first Burnside `pᵃqᵇ` in Lean.**

## Q3. Closing the one gap (3): `∑_χ χ(1)·χ(g) = 0` for `g ≠ 1`

This is the `(g, 1)` case of column orthogonality. Two formalizable routes; mathlib has
**neither** packaged, so either is a genuine (few-hundred-line) infrastructure lap.

### Route A — full second orthogonality (mirror mathcomp / textbook) — now well-supported
Build `second_orthogonality_relation`: the character table is a **square** matrix
(rows = irreducibles, cols = classes), row-orthonormal ⟹ (scaled) unitary ⟹ columns
orthogonal. The square-ness prerequisite `#Irr(G) = #ConjClasses(G)` (mathcomp `NirrE`)
**is now derivable from existing mathlib** via the Wedderburn–Artin decomposition above —
update-3's "build completeness from scratch" worry is overstated. Sketch:
* `ℂ[G] ≃ₐ ∏ᵢ Mₐᵢ(ℂ)` (`exists_algEquiv_pi_matrix_of_isAlgClosed`) ⟹ the number of matrix
  factors `n` = number of iso-classes of simple `ℂ[G]`-modules = `#Irr(G)`, and `∑ᵢ dᵢ² = |G|`.
* `Z(∏ᵢ Mₐᵢ(ℂ)) ≅ ∏ᵢ Z(Mₐᵢ(ℂ)) = ℂⁿ` ⟹ `dim_ℂ Z(ℂ[G]) = n`.
* `Z(ℂ[G])` has the **class sums `{classSum C}` as a ℂ-basis** (a central element is exactly a
  class function) ⟹ `dim_ℂ Z(ℂ[G]) = #ConjClasses(G)`. The repo already has `classSum` +
  `classSum_central`; the missing bridge is just "the class sums are linearly independent and
  span `Z(ℂ[G])`."
* Therefore `#Irr(G) = n = #ConjClasses(G)`.
So Route A's real remaining work is the single bridge "`{classSum C}` is a basis of `Z(ℂ[G])`",
not a from-scratch completeness theory. Heavier than Route B but yields the *general* relation
and the satisfying `∑dᵢ²=|G|`.

### Route B — regular-representation identity (RECOMMENDED; targeted to exactly what's needed)
You only need the column-vs-identity case, which is precisely the **regular character**:
> `∑_{χ ∈ Irr(G)} χ(1)·χ(g) = χ_reg(g) = |G|·[g = 1]`,  hence `= 0` for `g ≠ 1`.
Two sub-lemmas:
1. **`χ_reg(g) = |G|·[g=1]`** — elementary: `χ_reg` is the permutation character of `G`
   acting on itself by left multiplication; its value at `g` is the number of fixed points
   `#{h : g·h = h}`, which is `|G|` if `g=1` and `0` otherwise. mathlib has `Rep.leftRegular`
   to build this on.
2. **`χ_reg = ∑_{χ∈Irr} χ(1)·χ`** — the regular rep decomposes as `⊕_χ V_χ^{⊕ dim V_χ}`
   (each irreducible appears with multiplicity = its degree). From Maschke (have) +
   multiplicity `= ⟨χ_reg, χ⟩ = χ(1)` (compute via `char_orthonormal`, have the row
   relation). The missing glue mathlib doesn't package: "character of a semisimple rep =
   `∑ (multiplicity)·(irreducible character)`" and a handle on the complete set `Irr(G)`.

**Recommendation:** Route B. It builds *only* what the Burnside contradiction consumes
(the regular character vanishing off the identity), avoids the `#Irr=#classes` /
class-function-basis detour, and the two sub-lemmas are individually small given mathlib's
Maschke + `char_orthonormal` + `leftRegular`. Keep mathcomp's `second_orthogonality_relation`
proof (`character.v`) as the fallback blueprint if Route B's "complete `Irr(G)`" handle
proves fiddly — that's the one shared sticking point (you need to index a complete,
duplicate-free set of irreducibles either way).

### Final assembly of the axiom `isSimpleGroup_centralizer_index_not_primePow` (Isaacs 3.9)
With (1)(2)(4)(5)(6) in hand and (3) via Route B, the proof of the axiom:
`G` simple non-abelian, `g ≠ 1` with `|gᴳ| = pᵏ` (`k ≥ 1`). For each `χ ∈ Irr(G)`, `χ≠1`:
if `p ∤ χ(1)` then `gcd(pᵏ, χ(1)) = 1`, so by (2)+gcd `χ(g)/χ(1) ∈ ℤ̄`, `|χ(g)/χ(1)| ≤ 1`
((`norm_character_le`), all conjugates too), so by Kronecker (4) `χ(g)=0` or `g` acts as a
scalar; `g` scalar in a faithful irreducible ⟹ `⟨g⟩ ≤` a proper normal subgroup (6),
impossible in a simple non-abelian group ⟹ `χ(g)=0`. Then by (3):
`0 = χ_reg(g) = ∑_χ χ(1)χ(g) = 1 + ∑_{χ≠1, p∤χ(1)} χ(1)·0 + ∑_{χ≠1, p|χ(1)} χ(1)χ(g)
   = 1 + p·θ`, with `θ = ∑_{χ≠1, p|χ(1)} (χ(1)/p)·χ(g) ∈ ℤ̄`. So `θ = -1/p ∈ ℤ̄`,
contradicting (5) `not_isIntegral_neg_inv_prime`. ∎  (Isaacs 3.9; this is precisely
mathcomp's `primes_class_simple_gt1`.)

---

### Bottom line
- The request is down to **one** missing brick, **(3) column orthogonality**; (2) is
  already done in-repo.
- mathlib has no column orthogonality (v4.29.1 = master here), BUT it **does** have the
  structural backbone — Maschke (`IsSemisimpleRing ℂ[G]`) + Wedderburn–Artin over alg-closed
  (`exists_algEquiv_pi_matrix_of_isAlgClosed`, i.e. `ℂ[G] ≅ ∏Mₐᵢ(ℂ)`). So this is a moderate
  build, not from-scratch. **Route B (regular character)** is the minimal targeted build for
  the specific relation; **Route A** (full second orthogonality) is now tractable too, its
  only real gap being "`{classSum C}` is a basis of `Z(ℂ[G])`".
- **Coq mathcomp `Burnside_p_a_q_b` (`group_representation/integral_char.v`, Isaacs 3.10) is
  a complete, structurally-identical formalization** — the decl-for-decl porting blueprint,
  including `second_orthogonality_relation` and `primes_class_simple_gt1` (= the repo's
  axiom). No Lean/Isabelle equivalent exists; this repo would be the first in Lean.

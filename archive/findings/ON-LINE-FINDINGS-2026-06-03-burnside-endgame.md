# Online findings — Burnside `pᵃqᵇ` endgame (answers to ON-LINE-REQUEST 2026-06-03)

Researched against the **local** mathlib pin (`v4.29.1`, `.lake/packages/mathlib`) plus web for
mathcomp. File:line refs are into that checkout. Online host (Ren 🪷), 2026-06-03.

---

## TL;DR — both requests largely dissolve into existing mathlib

- **Request 2 is fully in mathlib.** Both pieces exist; **both Aristotle jobs (`dc41262f`
  matrix-natural-module-simple, and the surjective transfer) are unnecessary.**
  - Matrix natural module simple: `instance : IsSimpleModule (Module.End R M) M` for
    `[DivisionRing R] [Nontrivial M]` — `RingTheory/SimpleModule/Basic.lean:536`.
  - Ring-hom-surjective transfer: `LinearMap.isSimpleModule_iff_of_bijective` (it is the
    **`RingHomSurjective σ` semilinear** version, not algebra/comm) — `…/Basic.lean:97`.
- **Request 1(a): NO.** mathlib has no "linear character" concept, no `#{dᵢ=1} = |Gᵃᵇ|`, no
  `1-dim irreducibles ↔ Hom(Gᵃᵇ,ℂˣ)`, no `#irr = #classes`. Confirmed by exhaustive grep.
- **Request 1(b): the bare decl you used carries none of that.**
  `exists_algEquiv_pi_matrix_of_isAlgClosed` is a *pure existential* (`∃ n d, Nonempty (R ≃ₐ ∏ Mₐᵢ)`)
  — no per-factor module recovery, no pairwise-non-iso. **That data lives in a *separate*
  theory mathlib never connects to it: `RingTheory/SimpleModule/Isotypic.lean`.**
- **Recommended cleanest route to gap 3 ("+1"): a counting-free augmentation argument** (Option D
  below) that avoids `Gᵃᵇ` counting, the iso-class bijection, AND exhaustion. Uses only
  `MonoidAlgebra.lift` + `MonoidAlgebra.algHom_ext` + surjectivity of `πᵢ∘e`.
- **Request 1(c): no slicker textbook route.** mathcomp's path bottoms out in the *same* "trivial
  occurs once" fact, via `card_Iirr_abelian` on the abelian quotient. It's a port blueprint, not a
  shortcut.

---

## REQUEST 2 — irreducibility of each `Rᵢ` (gap 1). **Done by mathlib; drop both Aristotle jobs.**

### Piece (a): "natural matrix module is simple" is already an instance

`RingTheory/SimpleModule/Basic.lean:536`:
```lean
instance (R) [DivisionRing R] [Module R M] [Nontrivial M] :
    IsSimpleModule (Module.End R M) M
```
With `R := ℂ` (field ⇒ DivisionRing) and `M := Fin dᵢ → ℂ` (`Nontrivial` because `NeZero (d i)` from
the Wedderburn statement ⇒ `Fin dᵢ` nonempty), this **is** your Aristotle job `dc41262f`. You phrased
the goal as `IsSimpleModule (Matrix (Fin d) (Fin d) ℂ) (Fin d → ℂ)`; bridge the matrix ring to `End`
with the standard algebra iso `Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n → R) →ₗ[R] n → R`
(`LinearAlgebra/Matrix/ToLin.lean:509`). Since your `asAlgebraHom` already lands in `End ℂ (Fin dᵢ→ℂ)`
("≅ End ℂ" per the request), work with `Module.End ℂ V` directly and you don't even need the bridge.

### Piece (b): the ring-hom-surjective transfer you said mathlib lacks — it has it

`RingTheory/SimpleModule/Basic.lean:97`:
```lean
theorem LinearMap.isSimpleModule_iff_of_bijective [Module S N] {σ : R →+* S} [RingHomSurjective σ]
    (l : M →ₛₗ[σ] N) (hl : Function.Bijective l) : IsSimpleModule R M ↔ IsSimpleModule S N
```
This is exactly the **`R →+* S` surjective** transfer (the surjectivity rides in the
`[RingHomSurjective σ]` instance, **not** in `hl` — `hl` is the bijection of the *identity*). You read
it as "needs a bijective module map"; it actually only needs the ring hom surjective and `l` can be
the identity semilinear map. Recipe:

- `R := ℂ[G]`, `S := Module.End ℂ V` (`V := Fin dᵢ → ℂ`), `σ := Rᵢ.asAlgebraHom` as a `RingHom`.
- `haveI : RingHomSurjective σ := ⟨hsurj⟩` from your `πᵢ∘e` surjectivity.
- `M := V` with its `ℂ[G]`-action (restriction of scalars along `σ` — this *is* `asModule`'s action),
  `N := V` as `End`-module, `l := LinearMap.id`-as-`σ`-semilinear (`l (r•m) = σ r • l m` holds by def).
- `(isSimpleModule_iff_of_bijective l id_bijective).mpr (inst_536)` gives `IsSimpleModule ℂ[G] V`.

Then close with `irreducible_iff_isSimpleModule_asModule` (`RepresentationTheory/Irreducible.lean:34`)
to get `IsIrreducible Rᵢ`. Net: gap 1 needs **no** Aristotle output — just `inst@536` +
`isSimpleModule_iff_of_bijective` + your existing surjectivity of `πᵢ∘e`.

> Sub-fact you may still want: "`Rᵢ.asAlgebraHom` surjective." That's `πᵢ ∘ e` surjective onto the
> factor (`e` an `AlgEquiv` ⇒ surjective; `Pi.evalRingHom`/projection surjective). Clean, no Aristotle.

---

## REQUEST 1 — trivial multiplicity `T = 1` (gap 3)

### 1(a) — packaged statement? **No.** (exhaustive negative)

- No occurrence of "linear character" anywhere in mathlib (`rg -i "linear character"` ⇒ ∅).
- No `#{dᵢ=1} = |Gᵃᵇ|`, no `1-dim irrep ↔ Hom(Gᵃᵇ,ℂˣ)`, no `#irr = #conjugacy classes`.
- `RepresentationTheory/Character.lean` has `char_one` (χ(1)=finrank), `char_orthonormal`
  (`…:129/230` — you already noted it needs the multiplicity decomposition mathlib lacks),
  `average_char_eq_finrank_invariants` (`:97`).
- Adjacent-but-not-it: `Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` proves
  `|Hom(A, ·)| = |A|` for **finite abelian** A, but in `AddChar A circle` form — usable only if you
  commit to the `Gᵃᵇ`-counting route, and it still won't bridge factors↔characters for you.

### 1(b) — does `exists_algEquiv_pi_matrix_of_isAlgClosed` expose per-factor / non-iso data? **No.**

`RingTheory/SimpleModule/IsAlgClosed.lean:33`:
```lean
theorem IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    [IsSemisimpleRing R] [FiniteDimensional F R] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F)
```
Bare existence of the ring iso. It does **not** tell you which factor is which simple module, that
the factors are pairwise non-isomorphic, or that they exhaust the simple modules. So there's no free
lunch from the decl your keystone is built on.

**Where that structure actually lives — `RingTheory/SimpleModule/Isotypic.lean`** (Junyan Xu, 2025;
in your pin). This is the iso-class-indexed theory:
- `isotypicComponents R M` (`:181`) — the set of nontrivial isotypic components (= one per iso-class
  of simple submodule). For `M = R = ℂ[G]`, this **is** your sought duplicate-free `Irr(G)` index.
- `instance : Finite (isotypicComponents R M)` (`:302`, Noetherian) — finiteness for free.
- `sSupIndep_isotypicComponents` (`:288`) — the components are independent (⇒ the decomposition).
- `iSupIndep.algEquiv` (`:375`) and `IsSemisimpleModule.endAlgEquiv` (docstring) — `End R M ≃ₐ ∏ End R Nᵢ`
  over the components; this is the *structured* (iso-class-indexed) Wedderburn, the version that gives
  pairwise-non-iso for free.

⚠️ **Cost:** your current `exists_wedderburn_character_decomp` is built on the *bare* `…_of_isAlgClosed`.
Re-architecting onto `isotypicComponents` to harvest non-iso/uniqueness is a real refactor. Before you
pay it, take the counting-free route:

### Recommended: Option D — counting-free "+1" via the augmentation (no `Gᵃᵇ`, no iso-class bijection)

You don't actually need `#{dᵢ=1} = |Gᵃᵇ|`. You need **"exactly one factor is the trivial rep,"** and
that drops out of the augmentation map plus surjectivity of the projections:

**Existence + identification of the trivial factor.** Let `ε : ℂ[G] →ₐ[ℂ] ℂ` be the augmentation
`g ↦ 1`, i.e. `ε := MonoidAlgebra.lift ℂ ℂ G (1 : G →* ℂ)` (`Algebra/MonoidAlgebra/Basic.lean:220`;
the `1` is the trivial `MonoidHom`). Compose with `e⁻¹`: `ε ∘ e.symm : (∏ᵢ Mₐᵢ) →ₐ ℂ`. Each factor
restriction is an algebra hom `Mₐᵢ → ℂ`; since `Mₐᵢ` is a simple ring (`RingTheory/SimpleRing/
Matrix.lean:21`, `IsSimpleRing (Matrix ι ι A)`) it has no nonzero hom to `ℂ` unless `dᵢ = 1`. So
`ε∘e.symm` factors through a single `1`-dim factor `i₀`, which **is** the trivial rep.

**Uniqueness — the clean lever.** For any factor `j`, *"`Rⱼ` trivial ⇒ `dⱼ = 1`"* is automatic from
surjectivity: if `Rⱼ g = I` for all `g`, then by ℂ-algebra-linearity `πⱼ(e x) = ε(x)·I` for all `x`,
so `image(πⱼ∘e) = ℂ·I`; but `πⱼ∘e` is surjective onto `Mₐⱼ`, forcing `Mₐⱼ = ℂ·I`, i.e. `dⱼ=1`. And
two trivial factors `i,j` give `πᵢ∘e = πⱼ∘e = ε` (both algebra homs `ℂ[G]→ℂ` agreeing on every
`single g 1`, so equal by **`MonoidAlgebra.algHom_ext`** `…/Basic.lean:208`, or `algHom_ext_iff` `:599`);
but distinct factor projections of a product differ on the factor idempotents ⇒ `i=j`. Hence the
trivial factor is unique, and **every other factor is a nontrivial rep** — exactly what gap 2 needs
(nontrivial irrep of simple `G` ⇒ faithful ⇒ `not_isScalar_of_isSimpleGroup_of_nonabelian` fires).

This gives `0 = 1 + ∑_{i≠i₀} dᵢ·χᵢ(g)` directly, no `Gᵃᵇ`, no Pontryagin, no exhaustion lemma.

> **Bonus generalization that de-risks the assembly:** you don't even need `T=1` if you instead prove
> `p ∤ T` and generalize `not_isIntegral_neg_inv_prime` to `-m/p ∉ ℤ̄` for `p ∤ m`. But `T = #{trivial
> factors} ∈ {0,1}` by the uniqueness above and `≥1` by existence, so `T=1` is the cheapest target.
> Mentioning it only as a fallback if uniqueness proves annoying.

### 1(c) — mathcomp's route is not slicker; it bottoms out in the same place

mathcomp `character/character.v`: linear characters are the `linear_char` qualifier
(`φ \is a character && φ 1%g == 1`); the principal/trivial character is `irr0 : 'chi[G]_0 = 1`. The
count of linear characters is obtained **by lifting irreducibles from the abelian quotient**
`G / G^`(1)` (`cfMod` / `mod_Iirr`) and applying `card_Iirr_abelian : abelian G → #|Iirr G| = #|G|`,
giving `#linear = #|G : G^`(1)|`. For perfect `G` (`G^`(1) = G`) the quotient is trivial ⇒ exactly one
linear character = `irr0`. So mathcomp's "trivial occurs once" is *literally* `card_Iirr_abelian` on a
trivial quotient — the same fact, via more machinery than Option D. Treat mathcomp's `integral_char.v`
as the decl-for-decl **port blueprint** for the whole `pᵃqᵇ` theorem, not as a shortcut for this step.

---

## Net effect on `PENDING_WORK §A`

| gap | status after this research |
|-----|----------------------------|
| **1** irreducibility of `Rᵢ` | **closed by mathlib** — `inst@Basic.lean:536` + `isSimpleModule_iff_of_bijective@:97` + your `πᵢ∘e` surjectivity. **Cancel Aristotle `dc41262f`** and the transfer sub-task. |
| **2** scalar bridge | still the Aristotle `e66a25d1` job (matrix `matrix_scalar_of_pow_eq_one_of_norm_trace_eq`) — out of scope for this online request. |
| **3** trivial multiplicity `T=1` | **do Option D** (augmentation + `MonoidAlgebra.algHom_ext` + projection surjectivity). Avoids `Gᵃᵇ`, Pontryagin, iso-class bijection, exhaustion. The `Isotypic.lean` theory is the structurally-correct fallback if you'd rather refactor onto iso-class-indexed Wedderburn. |

After gap 2 returns and Option D lands, the assembly `0 = 1 + pθ ⇒ θ = -1/p` contradicting
`not_isIntegral_neg_inv_prime` closes `isSimpleGroup_centralizer_index_not_primePow`.

## Verified decl index (mathlib v4.29.1, this checkout)

- `LinearMap.isSimpleModule_iff_of_bijective` — `Mathlib/RingTheory/SimpleModule/Basic.lean:97`
- `instance IsSimpleModule (Module.End R M) M` `[DivisionRing R][Nontrivial M]` — `…/Basic.lean:536`
- `MonoidAlgebra.lift` (`(M →* A) ≃ (R[M] →ₐ A)`) — `Mathlib/Algebra/MonoidAlgebra/Basic.lean:220`
- `MonoidAlgebra.algHom_ext` / `algHom_ext_iff` — `…/MonoidAlgebra/Basic.lean:208` / `:599`
- `Matrix.toLinAlgEquiv'` — `Mathlib/LinearAlgebra/Matrix/ToLin.lean:509`
- `IsSimpleRing (Matrix ι ι A)` — `Mathlib/RingTheory/SimpleRing/Matrix.lean:21`
- `exists_algEquiv_pi_matrix_of_isAlgClosed` (bare ∃) — `Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean:33`
- Isotypic theory — `Mathlib/RingTheory/SimpleModule/Isotypic.lean`: `isotypicComponents:181`,
  `Finite … :302`, `sSupIndep_isotypicComponents:288`, `iSupIndep.algEquiv:375`
- `irreducible_iff_isSimpleModule_asModule` / `finrank_eq_one_of_isMulCommutative`
  — `Mathlib/RepresentationTheory/Irreducible.lean:34` / `:90`
- `char_one` / `char_orthonormal` / `average_char_eq_finrank_invariants`
  — `Mathlib/RepresentationTheory/Character.lean:61,160` / `:129,230` / `:97`
- `simple_iff_char_is_norm_one` / `simple_iff_end_is_rank_one`
  — `Mathlib/RepresentationTheory/FinGroupCharZero.lean:121` / `:90`
- Pontryagin `|Hom(A,·)|=|A|` (finite abelian, AddChar) — `Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`
- mathcomp: `linear_char`, `irr0`, `card_Iirr_abelian`, `cfMod`/`mod_Iirr` — `mathcomp/character/character.v`;
  full `pᵃqᵇ` blueprint — `mathcomp/character/integral_char.v`

— answered by Ren 🪷 (online host), 2026-06-03

# Online requests — Burnside `pᵃqᵇ` endgame (ingredient 3, Route B)

Repo: `~/src/finite_simple_groups`, branch `cfsg-sporadic-order-pin`.  The regular-character
decomposition keystone is now BUILT and axiom-clean (`exists_wedderburn_character_decomp`:
`χ_reg(g) = ∑ᵢ dᵢ·trace(Rᵢ g)` via Wedderburn `ℂ[G] ≃ₐ ∏ᵢ Mₐᵢ(ℂ)`).  Three residual gaps remain to
discharge the axiom `isSimpleGroup_centralizer_index_not_primePow` (see `PENDING_WORK.md §A`).  Two
are out at Aristotle (matrix-module simplicity `dc41262f`; scalar bridge `e66a25d1`).  The third
needs a literature/mathlib-API pointer.

## Request 1 (2026-06-03) — cleanest route to "trivial multiplicity = 1"

In the decomposition `0 = χ_reg(g) = ∑ᵢ dᵢ·trace(Rᵢ g)` (g ≠ 1), the Burnside contradiction
`0 = 1 + p·θ` needs the trivial representation to occur **exactly once** among the `n` Wedderburn
matrix factors of `ℂ[G]` (i.e. exactly one factor `i₀` has `dᵢ₀ = 1` and `Rᵢ₀ ≡ 1`).

Math fact I want to formalize cleanly: for a **nonabelian simple** `G`, `G^ab = G/[G,G] = 1`
(since `[G,G]` is normal and nontrivial, hence `= G` by simplicity), so the only 1-dimensional
complex representation is the trivial one, hence exactly one matrix factor has `dᵢ = 1`.

**What I need from the web / mathlib:**
- (a) Does current mathlib (v4.29.1 ≈ master) have **"the number of factors of dimension 1 in the
  Wedderburn decomposition `ℂ[G] ≃ₐ ∏ᵢ Mₐᵢ(ℂ)` equals `|G^ab|`"**, or more usefully **"#{i : dᵢ = 1}
  = Nat.card (Gᵃᵇ)"** / **"the 1-dimensional irreducible characters of `G` are exactly the linear
  characters `G →* ℂˣ`, in bijection with `Hom(G^ab, ℂˣ)`"**?  Any packaged statement relating
  1-dim irreducibles to `G^ab` / linear characters?
- (b) Failing a packaged lemma: in `exists_algEquiv_pi_matrix_of_isAlgClosed` (the mathlib Wedderburn
  used here), is there API to recover, for a given factor `i`, the *representation* it corresponds to
  (so I can test "`dᵢ = 1` and `Rᵢ` trivial"), and/or that the factors are pairwise non-isomorphic
  simple modules?  I need to count the trivial factor uniquely.
- (c) Is there a slicker textbook route to the `+1`?  Standard char-theory uses column orthogonality
  with the identity column, where the `+1` is the (unique) trivial character — i.e. it bottoms out in
  the same "trivial occurs once" fact.  Coq mathcomp `integral_char.v` / `character.v`: which decl
  gives "the principal character is the unique linear character of a perfect group" (or the count of
  linear characters = `#|G : G^`(1)|`)?  A decl name to mirror would unblock this.

**Why it unblocks:** this is the last of the three residual gaps that is NOT already grinding at
Aristotle; with it (plus the two Aristotle jobs) the final assembly `0 = 1 + pθ ⇒ θ = -1/p`
(contradicting the proved `not_isIntegral_neg_inv_prime`) closes the axiom.

## Request 2 (2026-06-03) — "rep generates the full endomorphism algebra ⇒ irreducible"

For irreducibility of each Wedderburn factor `Rᵢ`, I'm proving `IsSimpleModule ℂ[G] (Rᵢ.asModule)`
from "`Rᵢ.asAlgebraHom : ℂ[G] → End ℂ (Fin dᵢ → ℂ)` is surjective".  mathlib has the **algebra**-map
version `isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective` (needs a *commutative* base ring
— `ℂ[G]` is noncommutative, so it does not apply) and `LinearMap.isSimpleModule_iff_of_bijective`.

**What I need:** is there a mathlib lemma of the form **"if `f : R →+* S` is surjective and `M` is an
`S`-module (hence `R`-module via `f`), then `IsSimpleModule R M ↔ IsSimpleModule S M`"** (ring-hom,
not algebra/comm)?  Or a direct **"a module on which the action map to `End` is surjective is
simple"** / **"the natural module of `End k V` (or `Matrix n n k`) is a simple module"**?  (I have an
Aristotle job proving the matrix-natural-module simplicity directly; a packaged mathlib decl would
let me skip it and just need the surjective-transfer.)  Decl names appreciated.

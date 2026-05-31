import FiniteSimpleGroups.Components

/-!
# `E(G)` is normal — transport lemmas (IN PROGRESS, contains `sorry`)

The payoff theorem for the layer is **`layer_normal : (layer G).Normal`**:
conjugation permutes the components, so their join `E(G)` is conjugation-stable,
hence normal. Reaching it needs two transport facts, neither in mathlib:

* **quasisimple is a `MulEquiv` invariant** (`IsQuasisimple.ofMulEquiv`) — this file;
* **subnormal is stable under conjugation** (next file).

⚠️ **This file currently contains two `sorry`s** in the proofs below. The statements
and proof *structure* are in place and the mathlib bricks are located (see the
docstrings), but two coercion-level steps (`MulEquiv` vs `MonoidHom` coe in
`map_center_eq`; the `QuotientGroup.congr` argument elaboration in `ofMulEquiv`) need
REPL iteration that the current environment's scrambled tool relay made unreliable.
Committed deliberately with disclosed `sorry`s rather than a false-green claim — the
next session finishes the two steps. Exact remaining errors are in the handoff doc
`HANDOFF-2026-05-31-layer-normal.md`.
-/

namespace FiniteSimpleGroups

open Subgroup (center)

/-- An isomorphism carries the center onto the center: `(center Q).map e = center Q'`.
mathlib has `Subgroup.centerCongr` (the centers are isomorphic) but not this
subgroup-image equality, which is what `QuotientGroup.congr` needs.

Proof sketch (working modulo a `MulEquiv`/`MonoidHom` coe normalization that `rw
[map_mul]` is currently not matching — `e w` vs `↑e x` appear in different coe forms
after `rintro`/`obtain`): forward, `z = e x` with `x ∈ center`, and for any `y = e w`,
`e w * e x = e (w*x) = e (x*w) = e x * e w`; backward, `e.symm z ∈ center` via
`e.injective` + `hz (e g)`. -/
private theorem map_center_eq {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (center Q).map (e : Q →* Q') = center Q' := by
  sorry

/-- **Quasisimple is a `MulEquiv` invariant.** If `Q ≃* Q'` and `Q` is quasisimple,
so is `Q'`: perfectness transports by `Group.IsPerfect.ofSurjective` (an iso is
surjective), and the simple central quotient transports by `QuotientGroup.congr`
(carrying `Q ⧸ Z(Q)` to `Q' ⧸ Z(Q')` via `map_center_eq`) plus
`MulEquiv.isSimpleGroup`.

⚠️ The perfect half is complete; the simple-central-quotient half is `sorry` pending
the `QuotientGroup.congr e (map_center_eq e)` elaboration (the `he : G'.map e = H'`
argument's coe form). -/
theorem IsQuasisimple.ofMulEquiv {Q Q' : Type*} [Group Q] [Group Q']
    [h : IsQuasisimple Q] (e : Q ≃* Q') : IsQuasisimple Q' := by
  refine ⟨?_, ?_⟩
  · -- perfect (complete)
    haveI := h.isPerfect
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · -- simple central quotient (pending coe elaboration)
    haveI := h.isSimpleGroup_quotient_center
    sorry

end FiniteSimpleGroups

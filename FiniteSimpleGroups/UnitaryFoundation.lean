import Mathlib

/-!
# Foundation for `PSU(n,q)`: the Hermitian base field `F_{q²}` with Frobenius star

`PSU_n(F_q)` is `SU_n(F_{q²}) / center`, where the unitary group is taken with respect to the
**Hermitian** form built from the order-2 Galois automorphism of `F_{q²}/F_q` — i.e. the
`q`-power Frobenius `x ↦ x^q`, an involution on `F_{q²}` (since `(x^q)^q = x^{q²} = x`).

mathlib's `Matrix.specialUnitaryGroup n α` is defined for any `[Field α] [StarRing α]` using
`star`. To instantiate it for the finite unitary groups we must equip `F_{q²}` with the Frobenius
as its `StarRing` structure — which mathlib does NOT provide for finite fields. This file supplies
it for the prime case `q = p` (base field `F_{p²} = GaloisField p 2`, `star x = x^p`) on a type
synonym, so there is no risk of a global `Star` diamond on `GaloisField`.

This is step 0 of the PSU thread (see `PENDING_WORK.md §G`): once `F_{p²}` is a `StarRing`,
`Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)` is the concrete `SU_n(p)`, and
`PSU n p := … ⧸ center` connects the currently-`opaque` `LieType.PSU`.
-/

open Polynomial

namespace FiniteSimpleGroups.PSU

/-- The Hermitian base field `F_{p²}` for `PSU_n(F_p)`, as a type synonym of `GaloisField p 2`
carrying the Frobenius `x ↦ x^p` as its `star`. -/
def UnitaryField (p : ℕ) [Fact p.Prime] : Type := GaloisField p 2

namespace UnitaryField

variable (p : ℕ) [Fact p.Prime]

noncomputable instance : Field (UnitaryField p) := inferInstanceAs (Field (GaloisField p 2))
instance : Finite (UnitaryField p) := inferInstanceAs (Finite (GaloisField p 2))
noncomputable instance : Fintype (UnitaryField p) := Fintype.ofFinite _
instance : CharP (UnitaryField p) p := inferInstanceAs (CharP (GaloisField p 2) p)

/-- `|F_{p²}| = p²`. -/
theorem card_eq : Fintype.card (UnitaryField p) = p ^ 2 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card p 2 (by norm_num)

/-- The Frobenius `x ↦ x^p` is the Hermitian conjugation. -/
noncomputable instance : Star (UnitaryField p) := ⟨fun x => frobenius (UnitaryField p) p x⟩

theorem star_eq (x : UnitaryField p) : star x = frobenius (UnitaryField p) p x := rfl

theorem star_pow (x : UnitaryField p) : star x = x ^ p := by
  rw [star_eq, frobenius_def]

/-- The Frobenius is an **involution** on `F_{p²}`: `(x^p)^p = x^{p²} = x`. -/
noncomputable instance : InvolutiveStar (UnitaryField p) where
  star_involutive x := by
    rw [star_pow, star_pow, ← pow_mul, ← sq, ← card_eq p]
    exact FiniteField.pow_card x

/-- `F_{p²}` is a `StarRing` with the Frobenius conjugation: `star` is a multiplicative,
additive involution (additivity is the Frobenius/`add_pow_char`, multiplicativity is field
commutativity). This is the Hermitian structure underlying `SU_n(F_p)`. -/
noncomputable instance : StarRing (UnitaryField p) where
  star_involutive := star_involutive
  star_mul x y := by
    rw [star_pow, star_pow, star_pow, mul_pow, mul_comm]
  star_add x y := by
    rw [star_pow, star_pow, star_pow, add_pow_char]

/-- Sanity: `star` is genuinely the nontrivial Frobenius, not the identity — `star x = x^p`. -/
theorem star_apply (x : UnitaryField p) : star x = x ^ p := star_pow p x

/-- `F_{p²}` as an `F_p = ZMod p`-algebra (inherited from `GaloisField p 2`). This exposes the
finite-field norm `Algebra.norm (ZMod p) : F_{p²} → F_p`, which equals the Hermitian norm
`x ↦ x · star x = x^{p+1}` (see `algebraMap_norm_eq_mul_star`). -/
noncomputable instance : Algebra (ZMod p) (UnitaryField p) :=
  inferInstanceAs (Algebra (ZMod p) (GaloisField p 2))

/-- **The Hermitian norm is the field norm**: `algebraMap (Algebra.norm c) = c · star c`. Both are
`c^{p+1}`: the field-norm exponent is `(|F_{p²}|−1)/(|F_p|−1) = (p²−1)/(p−1) = p+1`, and
`c · star c = c · c^p = c^{p+1}`. -/
theorem algebraMap_norm_eq_mul_star (c : UnitaryField p) :
    (algebraMap (ZMod p) (UnitaryField p)) (Algebra.norm (ZMod p) c) = c * star c := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcardK' : Nat.card (UnitaryField p) = p ^ 2 := by
    rw [Nat.card_eq_fintype_card]; exact card_eq p
  have hcardK : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hE : (Nat.card (UnitaryField p) - 1) / (Nat.card (ZMod p) - 1) = p + 1 := by
    rw [hcardK', hcardK, show p ^ 2 - 1 = (p + 1) * (p - 1) from by simpa using sq_tsub_sq p 1,
      Nat.mul_div_cancel _ (by omega : 0 < p - 1)]
  rw [FiniteField.algebraMap_norm_eq_pow, hE, star_pow, pow_succ, mul_comm]

/-- **`−1` is a Hermitian norm**: there is `c ∈ F_{p²}` with `c · star c = −1`. (The finite-field
norm `F_{p²}* → F_p*` is surjective, and `−1 ∈ F_p`.) This is the seed of isotropic-vector
existence: `(c, 1, 0, …)` is then isotropic, since `star c · c + 1 = −1 + 1 = 0`. -/
theorem exists_norm_neg_one : ∃ c : UnitaryField p, c * star c = -1 := by
  obtain ⟨c, hc⟩ := FiniteField.norm_surjective (ZMod p) (UnitaryField p) (-1)
  exact ⟨c, by rw [← algebraMap_norm_eq_mul_star, hc, map_neg, map_one]⟩

end UnitaryField

/-- **The concrete special unitary group `SU_n(F_p)`** — now well-formed because `UnitaryField p`
is a `StarRing`. This is the linear group whose center-quotient is `PSU_n(F_p)`; it connects the
currently-`opaque` `LieType.PSU` (step 0 of the PSU thread, `PENDING_WORK.md §G`). -/
noncomputable abbrev SU (n p : ℕ) [Fact p.Prime] : Type :=
  Matrix.specialUnitaryGroup (Fin n) (UnitaryField p)

/-- **The concrete projective special unitary group** `PSU_n(F_p) = SU_n(F_p) ⧸ center` — the
target to which the `opaque LieType.PSU` should be connected (replacing the `opaque` carrier and
the `[Group (PSU n q)]` axiom argument). Both `SU` and its center-quotient inherit `Group`
instances (sanity-confirmed by `psuConcrete_group` below). -/
noncomputable abbrev PSUConcrete (n p : ℕ) [Fact p.Prime] : Type :=
  SU n p ⧸ Subgroup.center (SU n p)

/-- `SU_n(F_p)` is a group (mathlib's `specialUnitaryGroup` group instance, `star = inv`), so its
center-quotient `PSUConcrete` is too. -/
theorem psuConcrete_group (n p : ℕ) [Fact p.Prime] : Nonempty (Group (PSUConcrete n p)) :=
  ⟨inferInstance⟩

end FiniteSimpleGroups.PSU

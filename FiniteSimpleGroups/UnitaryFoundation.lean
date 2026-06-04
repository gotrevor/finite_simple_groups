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

open Matrix in
/-- **Isotropic vectors exist** for the standard Hermitian form on `(F_{p²})ⁿ`, `n ≥ 2`: the
vector `v = c·e₀ + e₁` (with `c·star c = −1` from `exists_norm_neg_one`) is nonzero and isotropic,
since `⟨v,v⟩ = star v ⬝ᵥ v = star c · c + 1 = c · star c + 1 = 0`. This is the nonemptiness input
to the `PSU`-action on isotropic projective points (step 2). -/
theorem exists_isotropic (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : Fin n → UnitaryField p, v ≠ 0 ∧ star v ⬝ᵥ v = 0 := by
  obtain ⟨c, hc⟩ := exists_norm_neg_one p
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp only [i₀, i₁, ne_eq, Fin.mk.injEq]; omega
  refine ⟨Pi.single i₀ c + Pi.single i₁ 1, ?_, ?_⟩
  · intro h
    have h1 := congrFun h i₁
    rw [Pi.add_apply, Pi.single_eq_of_ne hne.symm, Pi.single_eq_same, Pi.zero_apply,
      zero_add] at h1
    exact one_ne_zero h1
  · rw [star_add, ← Pi.single_star, ← Pi.single_star, star_one]
    simp only [add_dotProduct, dotProduct_add, single_dotProduct,
      Pi.single_eq_same, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm,
      mul_one, mul_zero, add_zero, zero_add]
    rw [mul_comm (star c) c, hc]
    ring

/-- **The Frobenius conjugation is nontrivial**: there is `b ∈ F_{p²}` with `star b ≠ b` (i.e.
`b ∉ F_p`). The order of the Frobenius `AlgHom` is `finrank = 2 ≠ 1`, so it is not the identity. -/
theorem exists_star_ne_self : ∃ b : UnitaryField p, star b ≠ b := by
  have hfin : Module.finrank (ZMod p) (UnitaryField p) = 2 :=
    GaloisField.finrank p (by norm_num)
  have horder : orderOf (FiniteField.frobeniusAlgHom (ZMod p) (UnitaryField p)) = 2 := by
    rw [FiniteField.orderOf_frobeniusAlgHom, hfin]
  have hfrob : ∀ b : UnitaryField p,
      FiniteField.frobeniusAlgHom (ZMod p) (UnitaryField p) b = star b := by
    intro b
    show b ^ (Fintype.card (ZMod p)) = star b
    rw [ZMod.card, star_pow]
  have hne1 : FiniteField.frobeniusAlgHom (ZMod p) (UnitaryField p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    exact absurd horder (by norm_num)
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  exact hne1 (AlgHom.ext fun x => by rw [AlgHom.one_apply, hfrob, hcon])

/-- **The trace-zero (skew-Hermitian) scalars are nontrivial**: there is a nonzero `a` with
`a + star a = 0`. From some `b` with `star b ≠ b` (`exists_star_ne_self`), `a = b − star b ≠ 0`
is trace-zero (`star a = star b − b = −a`). This makes the unitary root subgroup `uRootSubgroup`
nontrivial — the nondegeneracy input to the `PSU` Iwasawa structure (step 3). -/
theorem exists_traceZero_ne_zero : ∃ a : UnitaryField p, a ≠ 0 ∧ a + star a = 0 := by
  obtain ⟨b, hb⟩ := exists_star_ne_self p
  refine ⟨b - star b, ?_, ?_⟩
  · intro h
    rw [sub_eq_zero] at h
    exact hb h.symm
  · rw [star_sub, star_star]; ring

/-- **Two distinct Hermitian-norm `−1` elements.** The norm-`(−1)` fibre is a coset of the norm-one
group (order `p+1 ≥ 2`), so it has more than one element. Concretely: `c` with `N(c) = −1`
(`exists_norm_neg_one`) and `c·ζ` where `ζ = b·(star b)⁻¹` has norm one and `ζ ≠ 1` (from
`star b ≠ b`). This is the seed for spanning the space by isotropic vectors (`UnitarySimple`). -/
theorem exists_two_norm_neg_one :
    ∃ c c' : UnitaryField p, c ≠ c' ∧ c * star c = -1 ∧ c' * star c' = -1 := by
  obtain ⟨c, hc⟩ := exists_norm_neg_one p
  obtain ⟨b, hb⟩ := exists_star_ne_self p
  have hb0 : b ≠ 0 := fun h => hb (by rw [h, star_zero])
  have hsb0 : star b ≠ 0 := fun h => hb0 (by simpa using congrArg star h)
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hc; exact one_ne_zero (neg_eq_zero.mp hc.symm)
  set ζ : UnitaryField p := b * (star b)⁻¹ with hζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [hζ] at h
    field_simp [hsb0] at h
    exact hb h.symm
  have hNζ : ζ * star ζ = 1 := by
    rw [hζ, star_mul', star_inv₀, star_star]
    field_simp [hb0, hsb0]
  refine ⟨c, c * ζ, ?_, hc, ?_⟩
  · intro h
    apply hζ1
    have : c * 1 = c * ζ := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hc0 this).symm
  · rw [star_mul']
    calc (c * ζ) * (star c * star ζ) = (c * star c) * (ζ * star ζ) := by ring
      _ = -1 := by rw [hc, hNζ, mul_one]

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

import FiniteSimpleGroups.UnitaryFoundation

/-!
# Unitary transvections — PSU step 1

The transvection toolkit for the unitary family `PSU_n(F_q) = SU_n(F_{q²})/center`, mirroring
`SpTransvection.lean` for the symplectic family. We work over an arbitrary commutative `StarRing`
`α` (the Hermitian base field `F_{q²}` is the case `α = UnitaryField p`, where `star` is the
`q`-power Frobenius); the standard **Hermitian form** is `⟨x, y⟩ = (star x) ⬝ᵥ y`, and the unitary
group `Matrix.unitaryGroup n α = {U | U * star U = 1}` (with `star = conjTranspose`) is exactly its
isometry group.

For a vector `v` and scalar `a`, the **unitary transvection** is
`τ_{v,a}(x) = x + a·⟨v, x⟩·v`, realised as the matrix `1 + a • (v ⊗ star v)`
(`v ⊗ w = vecMulVec v w`). Its two defining facts:

* **`star (τ_{v,a}) = τ_{v, star a}`** — because the rank-one matrix `v ⊗ star v` is *Hermitian*.
* The transvections at a fixed `v` form a one-parameter family: `τ_{v,a}·τ_{v,b} = τ_{v,a+b}`
  whenever `v` is **isotropic** (`⟨v,v⟩ = star v ⬝ᵥ v = 0`), since then `(v ⊗ star v)² = 0`.

Together these give the membership criterion (the unitary analogue of `spTransvection_mem`):
`τ_{v,a}` lies in `unitaryGroup` iff `v` is isotropic and `a` is **trace-zero** (`a + star a = 0`),
because then `τ_{v,a}·star(τ_{v,a}) = τ_{v,a}·τ_{v,star a} = τ_{v, a + star a} = τ_{v,0} = 1`.
The determinant is automatically `1` for isotropic `v`, so `τ_{v,a} ∈ specialUnitaryGroup`.

This is step 1 of the PSU thread (`PENDING_WORK.md §G`); steps 2–3 (action on isotropic
ℙ-points, quasi-preprimitivity, the `MulAction.IwasawaStructure`) mirror `SpIwasawa.lean`.
-/

open Matrix

namespace FiniteSimpleGroups.PSU

variable {n : Type*} [DecidableEq n] [Fintype n] {α : Type*} [CommRing α] [StarRing α]

/-- The **unitary transvection** `τ_{v,a}` on `αⁿ` with respect to the standard Hermitian form
`⟨x,y⟩ = (star x) ⬝ᵥ y`: the map `x ↦ x + a·⟨v,x⟩·v`, realised as the matrix
`1 + a • (v ⊗ star v)` where `v ⊗ w = vecMulVec v w` is the outer product. -/
noncomputable def uTransvection (v : n → α) (a : α) : Matrix n n α :=
  1 + a • Matrix.vecMulVec v (star v)

omit [Fintype n] in
/-- `τ_{v,0} = 1` — the unit of the one-parameter family at `v`. -/
@[simp] theorem uTransvection_zero (v : n → α) : uTransvection v 0 = 1 := by
  simp [uTransvection]

/-- **The geometric action of a unitary transvection**: `τ_{v,a}(x) = x + a·⟨v,x⟩·v`, where
`⟨v,x⟩ = (star v) ⬝ᵥ x` is the Hermitian form. The defining property, foundation for the
action on isotropic points and the Steinberg/commutator relations toward `SU`-generation. -/
theorem uTransvection_mulVec (v : n → α) (a : α) (x : n → α) :
    uTransvection v a *ᵥ x = x + (a * (star v ⬝ᵥ x)) • v := by
  rw [uTransvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

omit [DecidableEq n] [Fintype n] in
/-- **The rank-one core `v ⊗ star v` is Hermitian** (self-adjoint): `star (v ⊗ star v) = v ⊗ star v`.
This is what makes `star (τ_{v,a}) = τ_{v, star a}` and underlies the membership criterion. -/
theorem star_vecMulVec_star (v : n → α) :
    star (Matrix.vecMulVec v (star v)) = Matrix.vecMulVec v (star v) := by
  rw [star_eq_conjTranspose, conjTranspose_vecMulVec, star_star]

/-- **Hermitian adjoint of a unitary transvection**: `star (τ_{v,a}) = τ_{v, star a}`. Immediate
from the Hermitian-ness of `v ⊗ star v`; holds for *every* `v` and `a` (no isotropy needed). -/
theorem uTransvection_star (v : n → α) (a : α) :
    star (uTransvection v a) = uTransvection v (star a) := by
  simp only [uTransvection, star_add, star_one, star_eq_conjTranspose, conjTranspose_smul]
  rw [← star_eq_conjTranspose, star_vecMulVec_star]

/-- **The one-parameter family at an isotropic `v`**: `τ_{v,a}·τ_{v,b} = τ_{v,a+b}`. The nilpotency
`(v ⊗ star v)² = 0` follows from isotropy `⟨v,v⟩ = (star v) ⬝ᵥ v = 0`. This is the abelian "root
subgroup" feeding the Iwasawa structure on `PSU`. -/
theorem uTransvection_mul (v : n → α) (a b : α) (hv : star v ⬝ᵥ v = 0) :
    uTransvection v a * uTransvection v b = uTransvection v (a + b) := by
  have hNN : Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hv, zero_smul, vecMulVec_zero]
  simp only [uTransvection, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hNN, smul_zero, add_zero, add_smul]
  abel

/-- **A unitary transvection lies in the unitary group** when `v` is isotropic
(`⟨v,v⟩ = star v ⬝ᵥ v = 0`) and `a` is trace-zero (`a + star a = 0`): then
`τ_{v,a}·star(τ_{v,a}) = τ_{v,a}·τ_{v,star a} = τ_{v, a + star a} = τ_{v,0} = 1`. The unitary
analogue of `spTransvection_mem`. -/
theorem uTransvection_mem (v : n → α) (a : α) (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0) :
    uTransvection v a ∈ Matrix.unitaryGroup n α := by
  rw [Matrix.mem_unitaryGroup_iff, uTransvection_star, uTransvection_mul v a (star a) hv, ha,
    uTransvection_zero]

/-- **A unitary transvection has determinant 1** for isotropic `v` — so it lies in `SL` too. The
matrix determinant lemma `det(1 + (a·v) ⊗ star v) = 1 + (star v) ⬝ᵥ (a·v) = 1 + a·⟨v,v⟩ = 1`. -/
theorem uTransvection_det (v : n → α) (a : α) (hv : star v ⬝ᵥ v = 0) :
    (uTransvection v a).det = 1 := by
  rw [uTransvection, ← smul_vecMulVec, vecMulVec_eq (ι := Unit),
    det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hv, smul_zero, add_zero]

/-- **A unitary transvection lies in the special unitary group** (`unitary` + `det = 1`) for
isotropic `v` and trace-zero `a`. The element-level home of `τ_{v,a}` for the `PSU` Iwasawa
structure. -/
theorem uTransvection_mem_su (v : n → α) (a : α) (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0) :
    uTransvection v a ∈ Matrix.specialUnitaryGroup n α :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨uTransvection_mem v a hv ha, uTransvection_det v a hv⟩

/-- **A transvection fixes its own centre**: `τ_{v,a}(v) = v` for isotropic `v` (since
`⟨v,v⟩ = 0`). -/
theorem uTransvection_apply_self (v : n → α) (a : α) (hv : star v ⬝ᵥ v = 0) :
    uTransvection v a *ᵥ v = v := by
  rw [uTransvection_mulVec, hv, mul_zero, zero_smul, add_zero]

/-- **The unitary group preserves the Hermitian form**: for `g ∈ unitaryGroup` and all `x, y`,
`⟨g·x, g·y⟩ = ⟨x,y⟩`, i.e. `star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y`. The defining isometry
property (`gᴴ g = 1`), via the adjoint identity `star (g·x) = star x ᵥ* gᴴ`. Keeps isotropic
vectors isotropic under the action — the geometric input to the `PSU`-action on isotropic points. -/
theorem u_preserves_form {g : Matrix n n α} (hg : g ∈ Matrix.unitaryGroup n α) (x y : n → α) :
    star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y := by
  have hgg : gᴴ * g = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hg
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hgg, one_mulVec]

/-- **The unitary action preserves isotropy**: if `v` is isotropic and `g ∈ unitaryGroup`, then
`g·v` is isotropic. So `g` carries the centre of `τ_{v,a}` to a valid centre `g·v`. -/
theorem u_isotropic_of_mem {g : Matrix n n α} (hg : g ∈ Matrix.unitaryGroup n α)
    {v : n → α} (hv : star v ⬝ᵥ v = 0) : star (g *ᵥ v) ⬝ᵥ (g *ᵥ v) = 0 := by
  rw [u_preserves_form hg, hv]

/-- **Conjugation equivariance (adjoint form).** For `g ∈ unitaryGroup`, `g · τ_{v,a} · gᴴ =
τ_{g·v, a}`. The rank-one factor `v ⊗ star v` conjugates to `(g·v) ⊗ ((star v) ᵥ* gᴴ)`, and
`(star v) ᵥ* gᴴ = star (g·v)` is the adjoint identity. The `gᴴ` form is what the group-level
coercion `(g⁻¹).val = star g.val = g.valᴴ` produces directly. -/
theorem uTransvection_conjH {g : Matrix n n α} (hg : g ∈ Matrix.unitaryGroup n α)
    (v : n → α) (a : α) :
    g * uTransvection v a * gᴴ = uTransvection (g *ᵥ v) a := by
  have hggH : g * gᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hg
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [uTransvection, uTransvection, mul_add, mul_one, mul_smul_comm, add_mul, hggH,
    smul_mul_assoc, mul_vecMulVec, vecMulVec_mul, vecMul_conjTranspose, star_star]

/-- **Conjugation equivariance of unitary transvections.** For `g ∈ unitaryGroup` and all `v, a`,
`g · τ_{v,a} · g⁻¹ = τ_{g·v, a}`. This is the conjugation input to the `PSU` Iwasawa structure
(the unitary analogue of `spTransvection_conj`), via `g⁻¹ = gᴴ`. -/
theorem uTransvection_conj {g : Matrix n n α} (hg : g ∈ Matrix.unitaryGroup n α)
    (v : n → α) (a : α) :
    g * uTransvection v a * g⁻¹ = uTransvection (g *ᵥ v) a := by
  have hggH : g * gᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hg
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.inv_eq_right_inv hggH, uTransvection_conjH hg]

/-- The unitary transvection packaged as an element of `specialUnitaryGroup n α` (for isotropic
`v` and trace-zero `a`). -/
noncomputable def uTransvecSU (v : n → α) (a : α) (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0) :
    Matrix.specialUnitaryGroup n α :=
  ⟨uTransvection v a, uTransvection_mem_su v a hv ha⟩

@[simp] theorem uTransvecSU_coe (v : n → α) (a : α) (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0) :
    (uTransvecSU v a hv ha : Matrix n n α) = uTransvection v a := rfl

/-! ### The trace-zero parameter group and the unitary root subgroup

Unlike the symplectic case, where `τ_{v,c}` is symplectic for *every* `c`, a unitary transvection
`τ_{v,a}` is unitary only for **trace-zero** `a` (`a + star a = 0`). These trace-zero (a.k.a.
skew-Hermitian) scalars form an additive subgroup `traceZero α`; the map `a ↦ τ_{v,a}` is then a
homomorphism `Multiplicative (traceZero α) →* SU` whose abelian range — the **root subgroup**
`uRootSubgroup v` — is conjugated by `g ∈ SU` to `uRootSubgroup (g·v)`. These are the `is_comm`
and `is_conj` inputs to the unitary Iwasawa structure on `PSU`. -/

/-- The **trace-zero (skew-Hermitian) scalars** `{a : a + star a = 0}` as an additive subgroup of
`α`. These are exactly the admissible transvection parameters; over `F_{q²}` (`star x = x^q`) they
are the kernel of the trace `x ↦ x + x^q` to `F_q`, an `F_q`-line. -/
def traceZero (α : Type*) [CommRing α] [StarRing α] : AddSubgroup α where
  carrier := {a | a + star a = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, star_add] at *; linear_combination ha + hb
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, star_neg] at *; linear_combination -ha

@[simp] theorem mem_traceZero {a : α} : a ∈ traceZero α ↔ a + star a = 0 := Iff.rfl

/-- **The unitary root-subgroup homomorphism** `Multiplicative (traceZero α) →* SU`,
`a ↦ τ_{v,a}`, for isotropic `v`. The one-parameter family law `τ_{v,a}·τ_{v,b} = τ_{v,a+b}`
(`uTransvection_mul`) makes it a homomorphism out of the abelian trace-zero group. -/
noncomputable def uTransvecHom (v : n → α) (hv : star v ⬝ᵥ v = 0) :
    Multiplicative (traceZero α) →* Matrix.specialUnitaryGroup n α where
  toFun a := uTransvecSU v (Multiplicative.toAdd a : traceZero α) hv
    (mem_traceZero.mp (Multiplicative.toAdd a).2)
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    simp only [Submonoid.coe_mul, uTransvecSU_coe]
    exact (uTransvection_mul v _ _ hv).symm)

/-- **The unitary root subgroup along an isotropic `v`** — the range of `uTransvecHom v`, the
abelian "long root" subgroup `{τ_{v,a} : a + star a = 0}`. The unitary analogue of
`spTransvecGroup`. -/
noncomputable def uRootSubgroup (v : n → α) (hv : star v ⬝ᵥ v = 0) :
    Subgroup (Matrix.specialUnitaryGroup n α) :=
  (uTransvecHom v hv).range

instance (v : n → α) (hv : star v ⬝ᵥ v = 0) : IsMulCommutative (uRootSubgroup v hv) := by
  unfold uRootSubgroup; infer_instance

/-- **Conjugation in the group**: `g · τ_{v,a} · g⁻¹ = τ_{g·v, a}` for `g ∈ SU`. The unitary
analogue of `spTransvecSp_conj`; uses `(g⁻¹).val = star g.val = g.valᴴ` to land on
`uTransvection_conjH`. -/
theorem uTransvecSU_conj (g : Matrix.specialUnitaryGroup n α) (v : n → α) (a : α)
    (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0) :
    g * uTransvecSU v a hv ha * g⁻¹
      = uTransvecSU ((g : Matrix n n α) *ᵥ v) a
          (u_isotropic_of_mem (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) hv) ha := by
  apply Subtype.ext
  have hcoeInv : ((g⁻¹ : Matrix.specialUnitaryGroup n α) : Matrix n n α) = (↑g)ᴴ := by
    rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star,
      Matrix.star_eq_conjTranspose]
  simp only [Submonoid.coe_mul, uTransvecSU_coe, hcoeInv]
  exact uTransvection_conjH (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) v a

end FiniteSimpleGroups.PSU

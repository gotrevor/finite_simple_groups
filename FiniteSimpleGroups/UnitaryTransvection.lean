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

omit [Fintype n] in
/-- **Scaling the centre reparametrizes the transvection**: `τ_{c·v, a} = τ_{v, a·(c·star c)}`,
where `c·star c = N(c)` is the norm to the fixed field. (`vecMulVec (c·v) (star (c·v)) =
(c·star c)·(v ⊗ star v)`.) Hence `uRootSubgroup` depends only on the line `[v]` — the
well-definedness for the projective transvection family — and the norm appears where the square
appeared symplectically. Holds for every `c, a` (no isotropy needed). -/
theorem uTransvection_smul_vec (c a : α) (v : n → α) :
    uTransvection (c • v) a = uTransvection v (a * (c * star c)) := by
  have hstar : star (c • v) = star c • star v := by
    funext i; simp [Pi.smul_apply, star_mul']
  rw [uTransvection, uTransvection, hstar, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul,
    mul_assoc]

/-- **Matrix inverse of a unitary transvection** at isotropic `v`: `τ_{v,a}⁻¹ = τ_{v,-a}`, since
`τ_{v,a}·τ_{v,-a} = τ_{v,0} = 1`. Holds at the matrix level for any `a` (isotropy gives `N²=0`). -/
theorem uTransvection_inv_eq {v : n → α} (hv : star v ⬝ᵥ v = 0) (a : α) :
    (uTransvection v a)⁻¹ = uTransvection v (-a) :=
  Matrix.inv_eq_right_inv (by rw [uTransvection_mul v a (-a) hv, add_neg_cancel, uTransvection_zero])

/-- **The commutator collapse for unitary transvections** — the perfectness engine. If `g ∈
unitaryGroup` scales the isotropic centre `v` by `λ` (`g·v = λ·v`), then
`[g, τ_{v,a}] = g τ_{v,a} g⁻¹ τ_{v,a}⁻¹ = τ_{v, (N(λ)−1)·a}` where `N(λ) = λ·star λ`. So whenever
`N(λ) ≠ 1`, every `τ_{v,b}` is such a commutator (`a = b/(N(λ)−1)`) — the unitary analogue of
`spTransvecSp_commutator`, with the **norm** `λ·star λ` replacing the square `λ²`. -/
theorem uTransvection_commutator {g : Matrix n n α} (hg : g ∈ Matrix.unitaryGroup n α)
    {v : n → α} {lam : α} (hgv : g *ᵥ v = lam • v) (hv : star v ⬝ᵥ v = 0) (a : α) :
    g * uTransvection v a * g⁻¹ * (uTransvection v a)⁻¹
      = uTransvection v ((lam * star lam - 1) * a) := by
  rw [uTransvection_conj hg, hgv, uTransvection_smul_vec, uTransvection_inv_eq hv,
    uTransvection_mul v _ _ hv]
  congr 1
  ring

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

/-- **Membership in the root subgroup**: `y ∈ uRootSubgroup v` iff `y = τ_{v,a}` for some
trace-zero `a`. The unitary analogue of `mem_spTransvecGroup`. -/
theorem mem_uRootSubgroup {v : n → α} (hv : star v ⬝ᵥ v = 0)
    {y : Matrix.specialUnitaryGroup n α} :
    y ∈ uRootSubgroup v hv ↔ ∃ (a : α) (ha : a + star a = 0), uTransvecSU v a hv ha = y := by
  rw [uRootSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨_, mem_traceZero.mp (Multiplicative.toAdd m).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Multiplicative.ofAdd (⟨a, mem_traceZero.mpr ha⟩ : traceZero α), rfl⟩

/-- **The root subgroup depends only on the centre vector** (the isotropy proof is irrelevant):
equal centres give equal root subgroups. -/
theorem uRootSubgroup_congr {v w : n → α} (h : v = w) (hv : star v ⬝ᵥ v = 0)
    (hw : star w ⬝ᵥ w = 0) : uRootSubgroup v hv = uRootSubgroup w hw := by
  subst h; rfl

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

/-- **Conjugation-equivariance of the root subgroup**: `g · (uRootSubgroup v) · g⁻¹ =
uRootSubgroup (g·v)` for `g ∈ SU`. The Iwasawa `is_conj` input (and exhibits `uRootSubgroup v`
as normal in the line stabiliser). Unitary analogue of `spTransvecGroup_conj`. -/
theorem uRootSubgroup_conj (g : Matrix.specialUnitaryGroup n α) {v : n → α}
    (hv : star v ⬝ᵥ v = 0) :
    (uRootSubgroup v hv).map (MulAut.conj g)
      = uRootSubgroup ((g : Matrix n n α) *ᵥ v)
          (u_isotropic_of_mem (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) hv) := by
  ext y
  simp only [Subgroup.mem_map, mem_uRootSubgroup]
  constructor
  · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (uTransvecSU_conj g v a hv ha).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨uTransvecSU v a hv ha, ⟨a, ha, rfl⟩, uTransvecSU_conj g v a hv ha⟩

/-! ### The Eichler / Siegel transformation (the `hT1` line-stabiliser engine)

For `x` **isotropic** (`⟨x,x⟩ = 0`) and `h ⊥ x` (`⟨x,h⟩ = 0`), and a scalar `μ` with
`μ + star μ = ⟨h,h⟩` (a *trace condition*, solvable as `μ = ⟨h,h⟩/2` since `⟨h,h⟩` is Hermitian),
the **Eichler (Siegel) transformation**
`E_{x,h,μ}(z) = z + ⟨x,z⟩·h − ⟨h,z⟩·x − μ·⟨x,z⟩·x`
is a special-unitary element **fixing `x`**. Realised as the rank-≤2 matrix update
`1 + (h ⊗ star x) − (x ⊗ star h) − μ·(x ⊗ star x)`. Two facts drive `hT1`:

* **`star E · E = 1`** (unitary): the only surviving product among the rank-one pieces is
  `(x⊗star h)·(h⊗star x) = ⟨h,h⟩·(x⊗star x)`, cancelling `(μ + star μ)·(x⊗star x)` exactly by the
  trace condition.
* **`det E = 1`**: `E = 1 + U·V` with `U,V` of inner dimension `2`, so by Weinstein–Aronszajn
  `det E = det(1 + V·U)` and `1 + V·U = !![1,0; −⟨h,h⟩,1]` is lower-triangular unipotent.

This is the unitary analogue of the symplectic `sp_transvecFixing_step`, but the unitary
transvection coefficient must be trace-zero, which the *single* transvection `τ_{h,·}` fails — the
Eichler element supplies the missing isometry. Together with a `τ_{x,c}` correction (whose `c` is
*automatically* trace-zero when `y,y'` are isotropic mates of `x`) it gives `Stab[x]`-transitivity
on isotropic points non-perpendicular to `[x]`. -/

/-- The **Eichler (Siegel) transformation** matrix `E_{x,h,μ} = 1 + (h ⊗ star x) − (x ⊗ star h)
− μ·(x ⊗ star x)`. Its geometric action is `z ↦ z + ⟨x,z⟩·h − ⟨h,z⟩·x − μ⟨x,z⟩·x`. -/
noncomputable def uEichler (x h : n → α) (μ : α) : Matrix n n α :=
  1 + Matrix.vecMulVec h (star x) - Matrix.vecMulVec x (star h) - μ • Matrix.vecMulVec x (star x)

/-- **The action of the Eichler transformation**: `E_{x,h,μ}(z) = z + ⟨x,z⟩·h − ⟨h,z⟩·x − μ⟨x,z⟩·x`,
where `⟨v,z⟩ = star v ⬝ᵥ z`. -/
theorem uEichler_mulVec (x h : n → α) (μ : α) (z : n → α) :
    uEichler x h μ *ᵥ z
      = z + (star x ⬝ᵥ z) • h - (star h ⬝ᵥ z) • x - (μ * (star x ⬝ᵥ z)) • x := by
  simp only [uEichler, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

/-- **The anisotropic `μ`-part of the Eichler transformation peels off as a transvection at `x`**:
`E_{x,h,μ} = E_{x,h,0} · τ_{x,−μ}` (for `⟨x,x⟩ = 0`, `⟨x,h⟩ = 0`). The two cross products
`(h⊗x̄)(x⊗x̄) = ⟨x,x⟩·(h⊗x̄)` and `(x⊗h̄)(x⊗x̄) = ⟨h,x⟩·(x⊗x̄)` both vanish (isotropy/orthogonality),
leaving exactly the `−μ·(x⊗x̄)` term. This reduces the Eichler-as-transvection-product question to
the *pure* (`μ = 0`) case `E_{x,h,0}`, isolating the trace-zero scalar correction `τ_{x,−μ}` as a
genuine transvection (`−μ` is trace-zero whenever `μ + star μ = ⟨h,h⟩` and `h` is isotropic). -/
theorem uEichler_eq_mul_transvection {x h : n → α} (μ : α)
    (hxx : star x ⬝ᵥ x = 0) (hxh : star x ⬝ᵥ h = 0) :
    uEichler x h μ = uEichler x h 0 * uTransvection x (-μ) := by
  have hhx : star h ⬝ᵥ x = 0 := by
    rw [show star h ⬝ᵥ x = star (star x ⬝ᵥ h) by
      simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm], hxh,
      star_zero]
  simp only [uEichler, uTransvection, zero_smul, sub_zero, neg_smul,
    Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hxx, hhx, vecMulVec_zero]
  abel

/-- **The pure (`μ = 0`) Eichler transformation with an isotropic, orthogonal second vector `h` is an
explicit product of THREE unitary transvections.** For `⟨x,x⟩ = ⟨h,h⟩ = ⟨x,h⟩ = 0` and a trace-zero
unit `c` (`c·d = 1`, `star d = −d`, so `d = c⁻¹` over a field with `star c = −c`),
`E_{x,h,0} = τ_{h,d} · τ_{x,−c} · τ_{x+d·h, c}`.

This is the **"Eichler-as-transvection-product"** brick of the Dieudonné generation proof (the prior
`uEichler_eq_mul_transvection` reduced the general Eichler to this pure `μ = 0` case). The structural
insight that makes it work with NO ambient hyperbolic partner: the three centres `x`, `h`,
`x+d·h` are pairwise- and self-orthogonal isotropic, so **every `vecMulVec` cross-product vanishes**
(`P·Q = P·R = Q·R = 0` for `P = h⊗h̄`, `Q = x⊗x̄`, `R = (x+d·h)⊗(x+d·h)̄`), collapsing the triple
product to `1 + c·R − c·Q + d·P`; expanding `R` and using `c·d = 1` leaves exactly
`1 + h⊗x̄ − x⊗h̄ = E_{x,h,0}`. (Ref: Dieudonné, *La géométrie des groupes classiques*; Taylor,
*The Geometry of the Classical Groups* Ch. 11; the Eichler/Siegel transformation as a product of
transvections.) -/
theorem uEichler_isotropic_eq_transvection_prod {x h : n → α}
    (hxx : star x ⬝ᵥ x = 0) (hhh : star h ⬝ᵥ h = 0) (hxh : star x ⬝ᵥ h = 0)
    {c d : α} (hcd : c * d = 1) (hstard : star d = -d) :
    uEichler x h 0
      = uTransvection h d * uTransvection x (-c) * uTransvection (x + d • h) c := by
  have hhx : star h ⬝ᵥ x = 0 := by
    rw [show star h ⬝ᵥ x = star (star x ⬝ᵥ h) by
      simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm], hxh, star_zero]
  apply Matrix.ext_iff_mulVec.mpr
  intro z
  -- expand the triple-product action; the dotProduct of `x`/`h` with any `z + α•x + β•h` is just
  -- the dotProduct with `z` (the added pieces lie in the totally isotropic span `{x,h}`)
  simp only [← Matrix.mulVec_mulVec, uTransvection_mulVec, uEichler_mulVec,
    star_add, star_smul, hstard, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hxx, hhh, hxh, hhx, mul_zero, zero_mul, zero_smul, add_zero]
  -- both sides are now linear combinations of the atoms `x`, `h`, `z`; the scalar coefficients
  -- match after using `c·d = 1`
  -- both sides are linear combinations of the atoms `x`, `h`, `z`; the three scalar coefficients
  -- (of `z`, `h`, `x`) match after using `c·d = 1`
  match_scalars
  · ring
  · linear_combination (d * (star h ⬝ᵥ z) - star x ⬝ᵥ z) * hcd
  · linear_combination (star h ⬝ᵥ z) * hcd

/-- **Eichler composition law** (fixed isotropic centre `x`, second arguments `⊥ x`): the Eichler
transformations centred at `x` form a group under addition of their second argument, with a
`⟨a,b⟩`-cocycle in the scalar slot:
`E_{x,a,μ} · E_{x,b,ν} = E_{x, a+b, μ + ν + ⟨a,b⟩}`   (`⟨a,b⟩ = star a ⬝ᵥ b`).
This is the group law of the "long-root"/Eichler subgroup centred at `x`. It lets an Eichler with an
*anisotropic* `h` be split into two with *isotropic* second arguments (each then a transvection
product by `uEichler_isotropic_eq_transvection_prod`), once `h = h₁ + h₂` is a sum of two isotropic
vectors `⊥ x` — available when `dim x^⊥/⟨x⟩ ≥ 2` (i.e. `n ≥ 4`). -/
theorem uEichler_comp {x a b : n → α} (μ ν : α)
    (hxx : star x ⬝ᵥ x = 0) (hxa : star x ⬝ᵥ a = 0) (hxb : star x ⬝ᵥ b = 0) :
    uEichler x a μ * uEichler x b ν = uEichler x (a + b) (μ + ν + star a ⬝ᵥ b) := by
  have hax : star a ⬝ᵥ x = 0 := by
    rw [show star a ⬝ᵥ x = star (star x ⬝ᵥ a) by
      simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm], hxa, star_zero]
  apply Matrix.ext_iff_mulVec.mpr
  intro z
  simp only [← Matrix.mulVec_mulVec, uEichler_mulVec, star_add, dotProduct_add, add_dotProduct,
    dotProduct_sub, dotProduct_smul, smul_eq_mul,
    hxx, hxb, hax, mul_zero, sub_zero, add_zero]
  match_scalars <;> ring

/-- **The Eichler transformation fixes its isotropic centre `x`** (`⟨x,x⟩ = 0`, `⟨x,h⟩ = 0`): all
three correction coefficients `⟨x,x⟩`, `⟨h,x⟩`, `μ⟨x,x⟩` vanish. -/
theorem uEichler_apply_self (x h : n → α) (μ : α)
    (hxx : star x ⬝ᵥ x = 0) (hxh : star x ⬝ᵥ h = 0) :
    uEichler x h μ *ᵥ x = x := by
  have hhx : star h ⬝ᵥ x = 0 := by
    have hsw : star h ⬝ᵥ x = star (star x ⬝ᵥ h) := by
      simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm]
    rw [hsw, hxh, star_zero]
  rw [uEichler_mulVec, hxx, hhx]
  simp

/-- **The Eichler transformation is unitary** (`star E · E = 1`): under `⟨x,x⟩ = 0`, `⟨x,h⟩ = 0`
and the trace condition `μ + star μ = ⟨h,h⟩`, the cross term `(x⊗star h)(h⊗star x) = ⟨h,h⟩(x⊗star x)`
exactly cancels `(μ + star μ)(x⊗star x)`. -/
theorem uEichler_mem_unitary (x h : n → α) (μ : α)
    (hxx : star x ⬝ᵥ x = 0) (hxh : star x ⬝ᵥ h = 0)
    (hμ : μ + star μ = star h ⬝ᵥ h) :
    uEichler x h μ ∈ Matrix.unitaryGroup n α := by
  have hhx : star h ⬝ᵥ x = 0 := by
    have hsw : star h ⬝ᵥ x = star (star x ⬝ᵥ h) := by
      simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm]
    rw [hsw, hxh, star_zero]
  rw [Matrix.mem_unitaryGroup_iff']
  have hstarE : star (uEichler x h μ) = 1 + Matrix.vecMulVec x (star h)
      - Matrix.vecMulVec h (star x) - star μ • Matrix.vecMulVec x (star x) := by
    simp only [uEichler, star_eq_conjTranspose, conjTranspose_sub, conjTranspose_add,
      conjTranspose_one, conjTranspose_smul, conjTranspose_vecMulVec, star_star]
  rw [hstarE]
  show (1 + Matrix.vecMulVec x (star h) - Matrix.vecMulVec h (star x)
      - star μ • Matrix.vecMulVec x (star x)) * uEichler x h μ = 1
  rw [uEichler]
  set A := Matrix.vecMulVec h (star x) with hAdef
  set B := Matrix.vecMulVec x (star h) with hBdef
  set C := Matrix.vecMulVec x (star x) with hCdef
  -- the nine rank-one products; only `B * A` survives
  have hAA : A * A = 0 := by
    rw [hAdef, vecMulVec_mul_vecMulVec, hxh, zero_smul, vecMulVec_zero]
  have hAB : A * B = 0 := by
    rw [hAdef, hBdef, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  have hAC : A * C = 0 := by
    rw [hAdef, hCdef, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  have hBB : B * B = 0 := by
    rw [hBdef, vecMulVec_mul_vecMulVec, hhx, zero_smul, vecMulVec_zero]
  have hBC : B * C = 0 := by
    rw [hBdef, hCdef, vecMulVec_mul_vecMulVec, hhx, zero_smul, vecMulVec_zero]
  have hCA : C * A = 0 := by
    rw [hCdef, hAdef, vecMulVec_mul_vecMulVec, hxh, zero_smul, vecMulVec_zero]
  have hCB : C * B = 0 := by
    rw [hCdef, hBdef, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  have hCC : C * C = 0 := by
    rw [hCdef, vecMulVec_mul_vecMulVec, hxx, zero_smul, vecMulVec_zero]
  have hBA : B * A = (star h ⬝ᵥ h) • C := by
    rw [hBdef, hAdef, hCdef, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  -- expand the product, kill the zero terms, collect the `C` coefficient
  have key : (1 + B - A - star μ • C) * (1 + A - B - μ • C)
      = 1 + ((star h ⬝ᵥ h) - μ - star μ) • C := by
    simp only [add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, hAA, hAB, hAC, hBB, hBC, hCA, hCB, hCC, hBA, smul_zero, add_zero, sub_zero]
    rw [sub_smul, sub_smul]
    abel
  rw [key, show (star h ⬝ᵥ h) - μ - star μ = (0 : α) by linear_combination -hμ, zero_smul,
    add_zero]

/-- **The Eichler transformation has determinant 1** (`⟨x,x⟩ = 0`, `⟨x,h⟩ = 0`): writing
`E = 1 + U·V` with `U,V` of inner dimension `2`, Weinstein–Aronszajn gives `det E = det(1 + V·U)`
with `1 + V·U = !![1,0; −⟨h,h⟩,1]`. -/
theorem uEichler_det (x h : n → α) (μ : α)
    (hxx : star x ⬝ᵥ x = 0) (hxh : star x ⬝ᵥ h = 0) :
    (uEichler x h μ).det = 1 := by
  have hhx : star h ⬝ᵥ x = 0 := by
    have hsw : star h ⬝ᵥ x = star (star x ⬝ᵥ h) := by
      simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm]
    rw [hsw, hxh, star_zero]
  set w : n → α := -star h - μ • star x with hw
  set U : Matrix n (Fin 2) α := Matrix.of (fun i => ![h i, x i]) with hU
  set V : Matrix (Fin 2) n α := Matrix.of ![star x, w] with hV
  have hUV : uEichler x h μ = 1 + U * V := by
    rw [uEichler]
    ext i k
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      Matrix.mul_apply, Fin.sum_univ_two, hU, hV, hw, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul, Pi.star_apply, Pi.sub_apply,
      Pi.neg_apply, Pi.smul_apply]
    ring
  have hVU00 : (V * U) 0 0 = star x ⬝ᵥ h := by
    simp only [Matrix.mul_apply, hV, hU, Matrix.of_apply, Matrix.cons_val_zero, dotProduct]
  have hVU01 : (V * U) 0 1 = star x ⬝ᵥ x := by
    simp only [Matrix.mul_apply, hV, hU, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, dotProduct]
  have hVU10 : (V * U) 1 0 = w ⬝ᵥ h := by
    simp only [Matrix.mul_apply, hV, hU, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, dotProduct]
  have hVU11 : (V * U) 1 1 = w ⬝ᵥ x := by
    simp only [Matrix.mul_apply, hV, hU, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, dotProduct]
  have hwh : w ⬝ᵥ h = -(star h ⬝ᵥ h) := by
    rw [hw, sub_dotProduct, neg_dotProduct, smul_dotProduct, smul_eq_mul, hxh, mul_zero, sub_zero]
  have hwx : w ⬝ᵥ x = 0 := by
    rw [hw, sub_dotProduct, neg_dotProduct, smul_dotProduct, smul_eq_mul, hxx, mul_zero, sub_zero,
      hhx, neg_zero]
  rw [hUV, Matrix.det_one_add_mul_comm, Matrix.det_fin_two, Matrix.add_apply, Matrix.add_apply,
    Matrix.add_apply, Matrix.add_apply, hVU00, hVU01, hVU10, hVU11, hxx, hxh, hwh, hwx]
  rw [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq]
  ring

/-- **The Eichler transformation lies in `SU`** (`⟨x,x⟩ = 0`, `⟨x,h⟩ = 0`, `μ + star μ = ⟨h,h⟩`). -/
theorem uEichler_mem_su (x h : n → α) (μ : α)
    (hxx : star x ⬝ᵥ x = 0) (hxh : star x ⬝ᵥ h = 0)
    (hμ : μ + star μ = star h ⬝ᵥ h) :
    uEichler x h μ ∈ Matrix.specialUnitaryGroup n α :=
  Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨uEichler_mem_unitary x h μ hxx hxh hμ, uEichler_det x h μ hxx hxh⟩

/-! ### Pair-stabiliser bricks for the generation dimension-induction (`hgen`)

The Dieudonné/Eichler proof that transvections generate `SU` reduces a general `g ∈ SU` (via the
isotropic-vector transitivity and the line-stabiliser mate transitivity `hT1`, both transvection
products) to one **fixing a hyperbolic pair `(e,f)` pointwise**. Such a `g` then restricts to `SU`
on the orthogonal complement `⟨e,f⟩^⊥` (a nondegenerate Hermitian space of dimension `n-2`), where
transvections generate by induction and lift back to `V` (centres in `⟨e,f⟩^⊥`, so they fix `e,f`).
These are the two structural bricks of that reduction — unitary analogues of
`SpN.sp_fixing_preserves_perp` / `spTransvection_fixes_pair`. The remaining gap (mirroring the still
-open symplectic `sp_stab_hyperbolic_le`) is the dimension induction itself: the subspace→coordinates
restriction `SU(V) ⊇ Stab(e,f) ≅ SU(⟨e,f⟩^⊥)`. -/

/-- **A pair-fixing unitary preserves the orthogonal complement of `⟨e,f⟩`.** If `g ∈ unitaryGroup`
fixes `e` and `f`, it maps `⟨e,f⟩^⊥` into itself: `⟨e,x⟩ = ⟨f,x⟩ = 0 ⟹ ⟨e,g·x⟩ = ⟨f,g·x⟩ = 0`.
Via `g·e = e`, `g·f = f` and the isometry `u_preserves_form`. The "`g` restricts to `⟨e,f⟩^⊥`" half
of the generation induction. -/
theorem u_fixing_preserves_perp {g : Matrix n n α} (hg : g ∈ Matrix.unitaryGroup n α)
    {e f : n → α} (hge : g *ᵥ e = e) (hgf : g *ᵥ f = f) {x : n → α}
    (hex : star e ⬝ᵥ x = 0) (hfx : star f ⬝ᵥ x = 0) :
    star e ⬝ᵥ (g *ᵥ x) = 0 ∧ star f ⬝ᵥ (g *ᵥ x) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [← hge, u_preserves_form hg]; exact hex
  · rw [← hgf, u_preserves_form hg]; exact hfx

/-- **A transvection centred in `⟨e,f⟩^⊥` fixes the pair `(e,f)`.** If `⟨v,e⟩ = ⟨v,f⟩ = 0` then
`τ_{v,a}` fixes both `e` and `f` (each correction coefficient `a⟨v,·⟩` vanishes). The "extend back"
half: a transvection of the complement lands in the pair-stabiliser. -/
theorem uTransvection_fixes_pair {e f v : n → α} (a : α)
    (hve : star v ⬝ᵥ e = 0) (hvf : star v ⬝ᵥ f = 0) :
    uTransvection v a *ᵥ e = e ∧ uTransvection v a *ᵥ f = f := by
  refine ⟨?_, ?_⟩
  · rw [uTransvection_mulVec, hve, mul_zero, zero_smul, add_zero]
  · rw [uTransvection_mulVec, hvf, mul_zero, zero_smul, add_zero]

/-! ### Nontriviality of the root subgroup (over a field)

The Iwasawa structure requires the root subgroups to be *nontrivial*. Over a field, a transvection
`τ_{v,a}` is the identity only in the degenerate cases `v = 0` or `a = 0` (the rank-one term
`a·(v ⊗ star v)` vanishes iff `a = 0` or `v = 0`), so a nonzero trace-zero `a` at a nonzero `v`
gives `uRootSubgroup v ≠ ⊥`. Over `F_{q²}` such an `a` exists (`UnitaryField.exists_traceZero_ne_zero`)
and isotropic `v ≠ 0` exist for `n ≥ 2` (`UnitaryField.exists_isotropic`). -/

section Field
variable {F : Type*} [Field F] [StarRing F] {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- **A nontrivial transvection is not the identity** (over a field): for `v ≠ 0` and `a ≠ 0`,
`τ_{v,a} ≠ 1`, since `a·(v ⊗ star v) = 0` forces `a = 0` or `v = 0`. -/
theorem uTransvection_ne_one {v : ι → F} (hv : v ≠ 0) {a : F} (ha : a ≠ 0) :
    uTransvection v a ≠ 1 := by
  rw [uTransvection]
  intro h
  rw [add_eq_left, smul_eq_zero] at h
  rcases h with h | h
  · exact ha h
  · rw [vecMulVec_eq_zero] at h
    exact h.elim hv (fun h' => hv (star_eq_zero.mp h'))

/-- The packaged `SU`-element `τ_{v,a}` is `≠ 1` for `v ≠ 0`, `a ≠ 0` (isotropic, trace-zero). -/
theorem uTransvecSU_ne_one {v : ι → F} (hv : v ≠ 0) {a : F} (ha : a ≠ 0)
    (hiso : star v ⬝ᵥ v = 0) (htr : a + star a = 0) : uTransvecSU v a hiso htr ≠ 1 := fun h =>
  uTransvection_ne_one hv ha (by rw [← uTransvecSU_coe v a hiso htr, h]; rfl)

/-- **The root subgroup is nontrivial** at a nonzero isotropic `v`, given a nonzero trace-zero
scalar. This is the nondegeneracy input to the unitary Iwasawa structure on `PSU`. -/
theorem uRootSubgroup_ne_bot {v : ι → F} (hv : v ≠ 0) (hiso : star v ⬝ᵥ v = 0)
    (ha : ∃ a : F, a ≠ 0 ∧ a + star a = 0) : uRootSubgroup v hiso ≠ ⊥ := by
  obtain ⟨a, ha0, hatr⟩ := ha
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨uTransvecSU v a hiso hatr, ⟨Multiplicative.ofAdd ⟨a, hatr⟩, rfl⟩⟩, ?_⟩
  intro hh
  exact uTransvecSU_ne_one hv ha0 hiso hatr (by simpa using Subtype.ext_iff.mp hh)

/-- **The root subgroup depends only on the line `[v]`**: scaling `v` by a nonzero `c` leaves
`uRootSubgroup` unchanged (reparametrize the trace-zero `a ↦ a·N(c)`, `uTransvection_smul_vec`;
the norm `N(c) = c·star c` is a nonzero fixed-field scalar, so `a ↦ a·N(c)` is a trace-zero
bijection). Unitary analogue of `spTransvecGroup_smul`. -/
theorem uRootSubgroup_smul {c : F} (hc : c ≠ 0) {v : ι → F} (hv : star v ⬝ᵥ v = 0)
    (hcv : star (c • v) ⬝ᵥ (c • v) = 0) :
    uRootSubgroup (c • v) hcv = uRootSubgroup v hv := by
  have hcc : c * star c ≠ 0 := mul_ne_zero hc (star_ne_zero.mpr hc)
  have hccH : star (c * star c) = c * star c := by rw [star_mul', star_star, mul_comm]
  ext y
  rw [mem_uRootSubgroup, mem_uRootSubgroup]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a * (c * star c), ?_, ?_⟩
    · rw [star_mul', hccH, eq_neg_of_add_eq_zero_right ha]; ring
    · apply Subtype.ext
      rw [uTransvecSU_coe, uTransvecSU_coe]
      exact (uTransvection_smul_vec c a v).symm
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a * (c * star c)⁻¹, ?_, ?_⟩
    · have ht : star ((c * star c)⁻¹) = (c * star c)⁻¹ := by rw [star_inv₀, hccH]
      rw [star_mul', ht, eq_neg_of_add_eq_zero_right ha]; ring
    · apply Subtype.ext
      rw [uTransvecSU_coe, uTransvecSU_coe, uTransvection_smul_vec]
      congr 1
      rw [mul_assoc, inv_mul_cancel₀ hcc, mul_one]

/-- **The root subgroup of a representative of `[v]` equals that of `v`** (line-invariance for the
projective `Tline` family). Unitary analogue of `spTransvecGroup_rep`. -/
theorem uRootSubgroup_rep {v : ι → F} (hv : v ≠ 0) (hiso : star v ⬝ᵥ v = 0)
    (hrep : star (Projectivization.mk F v hv).rep ⬝ᵥ (Projectivization.mk F v hv).rep = 0) :
    uRootSubgroup ((Projectivization.mk F v hv).rep) hrep = uRootSubgroup v hiso := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F _ v (Projectivization.rep_nonzero _) hv).mp
    (Projectivization.mk_rep _)
  have hcne : c ≠ 0 := by
    rintro rfl; rw [zero_smul] at hc; exact (Projectivization.rep_nonzero _) hc.symm
  have hcviso : star (c • v) ⬝ᵥ (c • v) = 0 := by rw [hc]; exact hrep
  exact (uRootSubgroup_congr hc.symm hrep hcviso).trans (uRootSubgroup_smul hcne hiso hcviso)

end Field

/-- **Capstone (the Iwasawa data is live over `F_{p²}` for `n ≥ 2`)**: there is a nonzero isotropic
vector `v` whose root subgroup `uRootSubgroup v` is nontrivial. So the `PSU`-action set (isotropic
points) is nonempty AND each root subgroup is nondegenerate — the two existence inputs the unitary
Iwasawa structure needs, both now machine-checked. (Combines `UnitaryField.exists_isotropic` and
`UnitaryField.exists_traceZero_ne_zero` via `uRootSubgroup_ne_bot`.) -/
theorem exists_isotropic_uRootSubgroup_ne_bot (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) :
    ∃ (v : Fin n → UnitaryField p) (hiso : star v ⬝ᵥ v = 0),
      v ≠ 0 ∧ uRootSubgroup v hiso ≠ ⊥ := by
  obtain ⟨v, hv, hiso⟩ := UnitaryField.exists_isotropic p n hn
  exact ⟨v, hiso, hv, uRootSubgroup_ne_bot hv hiso (UnitaryField.exists_traceZero_ne_zero p)⟩

/-! ### The unitary scaling element on a hyperbolic pair

For the perfectness half of `PSU`-simplicity we need, for every isotropic `v`, an element of `SU`
that scales `v` by a scalar `λ` with `N(λ) ≠ 1` (then the commutator collapse
`uTransvection_commutator` turns every transvection into a commutator). Unlike `PSL`/`PSp`, the
unitary group preserves the form-type of a vector, so we cannot scale a standard basis vector and
conjugate; instead we build the scaling directly on the hyperbolic pair `(v, w)` supplied by
`exists_hyperbolic_partner`. This is the unitary analogue of the symplectic `spDiag`. -/

section Scaling

variable {N : Type*} [DecidableEq N] [Fintype N] {F : Type*} [Field F] [StarRing F]

/-- **Unitary scaling element on a hyperbolic pair `(v,w)`** (`⟨v,w⟩ = 1`, both isotropic): the
rank-2 update `1 + (λ-1)·(v ⊗ star w) + ((star λ)⁻¹-1)·(w ⊗ star v)` of the identity. It acts as
`v ↦ λ·v`, `w ↦ (star λ)⁻¹·w`, identity on `⟨v,w⟩^⊥`. -/
noncomputable def uScale (v w : N → F) (lam : F) : Matrix N N F :=
  1 + (lam - 1) • Matrix.vecMulVec v (star w) + ((star lam)⁻¹ - 1) • Matrix.vecMulVec w (star v)

/-- **The geometric action of the scaling element**:
`uScale v w λ (x) = x + (λ-1)·⟨w,x⟩·v + ((star λ)⁻¹-1)·⟨v,x⟩·w`. -/
theorem uScale_mulVec (v w : N → F) (lam : F) (x : N → F) :
    uScale v w lam *ᵥ x = x + ((lam - 1) * (star w ⬝ᵥ x)) • v
      + (((star lam)⁻¹ - 1) * (star v ⬝ᵥ x)) • w := by
  rw [uScale, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    op_smul_eq_smul, smul_smul, smul_smul]

/-- `uScale v w λ` scales `v` by `λ` (given the hyperbolic-pair relation `⟨w,v⟩ = 1` and `v`
isotropic). -/
theorem uScale_mulVec_self (v w : N → F) (lam : F) (hwv : star w ⬝ᵥ v = 1)
    (hviso : star v ⬝ᵥ v = 0) : uScale v w lam *ᵥ v = lam • v := by
  rw [uScale_mulVec, hwv, hviso, mul_one, mul_zero, zero_smul, add_zero,
    show (lam - 1) • v = lam • v - v by rw [sub_smul, one_smul], add_sub_cancel]

/-- `uScale v w λ` scales `w` by `(star λ)⁻¹` (given `⟨v,w⟩ = 1` and `w` isotropic). -/
theorem uScale_mulVec_partner (v w : N → F) (lam : F) (hvw : star v ⬝ᵥ w = 1)
    (hwiso : star w ⬝ᵥ w = 0) : uScale v w lam *ᵥ w = (star lam)⁻¹ • w := by
  rw [uScale_mulVec, hvw, hwiso, mul_one, mul_zero, zero_smul, add_zero,
    show ((star lam)⁻¹ - 1) • w = (star lam)⁻¹ • w - w by rw [sub_smul, one_smul], add_sub_cancel]

/-- **The scaling element is unitary** (`λ ≠ 0`, hyperbolic pair `(v,w)`). The rank-one factors
satisfy `A² = A`, `B² = B`, `AB = BA = 0` (where `A = v ⊗ star w`, `B = w ⊗ star v`), so
`uScale * star (uScale)` collapses to `1` with the two cross-coefficients vanishing identically. -/
theorem uScale_mem (v w : N → F) (lam : F) (hlam : lam ≠ 0)
    (hvw : star v ⬝ᵥ w = 1) (hwv : star w ⬝ᵥ v = 1)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0) :
    uScale v w lam ∈ Matrix.unitaryGroup N F := by
  have hAA : Matrix.vecMulVec v (star w) * Matrix.vecMulVec v (star w)
      = Matrix.vecMulVec v (star w) := by rw [vecMulVec_mul_vecMulVec, hwv, one_smul]
  have hBB : Matrix.vecMulVec w (star v) * Matrix.vecMulVec w (star v)
      = Matrix.vecMulVec w (star v) := by rw [vecMulVec_mul_vecMulVec, hvw, one_smul]
  have hAB : Matrix.vecMulVec v (star w) * Matrix.vecMulVec w (star v) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hwiso, zero_smul, vecMulVec_zero]
  have hBA : Matrix.vecMulVec w (star v) * Matrix.vecMulVec v (star w) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hviso, zero_smul, vecMulVec_zero]
  have hstar : star (uScale v w lam) = 1 + (star lam - 1) • Matrix.vecMulVec w (star v)
      + (lam⁻¹ - 1) • Matrix.vecMulVec v (star w) := by
    rw [uScale]
    simp only [star_add, star_one, star_eq_conjTranspose, conjTranspose_smul,
      conjTranspose_vecMulVec, star_star, star_sub, star_inv₀]
  have hlam' : star lam ≠ 0 := star_ne_zero.mpr hlam
  rw [Matrix.mem_unitaryGroup_iff, hstar, uScale]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hAA, hBB, hAB, hBA, smul_zero, add_zero]
  match_scalars <;> field_simp <;> ring

/-- **Determinant of the scaling element**: `det (uScale v w λ) = λ·(star λ)⁻¹`. By the
Weinstein–Aronszajn identity `det (1 + U V) = det (1 + V U)`, writing the rank-2 update as
`U V` with `U = [v | w]` (`N × 2`) and `V` the `2 × N` matrix of scaled coforms; then `V U` is the
`2 × 2` diagonal `diag(λ-1, (star λ)⁻¹-1)`, so `det (1 + V U) = λ·(star λ)⁻¹`. -/
theorem uScale_det (v w : N → F) (lam : F)
    (hvw : star v ⬝ᵥ w = 1) (hwv : star w ⬝ᵥ v = 1)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0) :
    (uScale v w lam).det = lam * (star lam)⁻¹ := by
  let U : Matrix N (Fin 2) F := Matrix.of (fun i => ![v i, w i])
  let V : Matrix (Fin 2) N F := Matrix.of (fun k j => (![(lam - 1) * star w j,
    ((star lam)⁻¹ - 1) * star v j] : Fin 2 → F) k)
  have key : ∀ (c : F) (a b : N → F), (∑ x, c * (star a) x * b x) = c * (star a ⬝ᵥ b) := by
    intro c a b; rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => mul_assoc _ _ _)
  have hUV : uScale v w lam = 1 + U * V := by
    ext i j
    simp only [uScale, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_apply, vecMulVec_apply,
      Pi.star_apply, U, V, smul_eq_mul]
    ring
  have hVU : V * U = !![lam - 1, 0; 0, (star lam)⁻¹ - 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.mul_apply, U, V, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      rw [key] <;>
      simp only [hwv, hwiso, hviso, hvw, mul_one, mul_zero]
  rw [hUV, Matrix.det_one_add_mul_comm, hVU]
  simp [Matrix.det_fin_two, Matrix.add_apply]

/-- **The scaling element lies in `SU`** when `λ` is in the fixed field (`star λ = λ`, `λ ≠ 0`):
then `det = λ·λ⁻¹ = 1`. This is the regime that feeds `PSU` perfectness (`N(λ) = λ²`, and one needs
`λ² ≠ 1`, i.e. a fixed-field scalar `≠ ±1`, available for `|F₀| ≥ 4`). -/
theorem uScale_mem_su (v w : N → F) (lam : F) (hlam : lam ≠ 0) (hfix : star lam = lam)
    (hvw : star v ⬝ᵥ w = 1) (hwv : star w ⬝ᵥ v = 1)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0) :
    uScale v w lam ∈ Matrix.specialUnitaryGroup N F :=
  Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨uScale_mem v w lam hlam hvw hwv hviso hwiso, by
      rw [uScale_det v w lam hvw hwv hviso hwiso, hfix, mul_inv_cancel₀ hlam]⟩

open scoped commutatorElement in
/-- **Each unitary transvection lies in the commutator subgroup of `SU`** — given a hyperbolic pair
`(v,w)` and a fixed-field scalar `λ` (`star λ = λ`) with `N(λ) = λ·star λ ≠ 1`. Indeed
`τ_{v,a} = ⁅g, τ_{v, a/(N(λ)-1)}⁆` where `g = uScale v w λ` scales `v` by `λ`
(`uScale_mem_su`/`uScale_mulVec_self`), by the commutator collapse `uTransvection_commutator`. The
unitary analogue of `SpN.spTransvecSp_mem_commutator`; the `N(λ)≠1` hypothesis is the honest
field-size condition (it fails for the small non-perfect unitary groups). -/
theorem uTransvecSU_mem_commutator (v w : N → F) (lam : F) (hlam : lam ≠ 0) (hfix : star lam = lam)
    (hN : lam * star lam ≠ 1)
    (hvw : star v ⬝ᵥ w = 1) (hwv : star w ⬝ᵥ v = 1)
    (hviso : star v ⬝ᵥ v = 0) (hwiso : star w ⬝ᵥ w = 0)
    (a : F) (ha : a + star a = 0) :
    uTransvecSU v a hviso ha ∈ commutator (Matrix.specialUnitaryGroup N F) := by
  have hne : lam * star lam - 1 ≠ 0 := sub_ne_zero.mpr hN
  have hDfix : star (lam * star lam - 1) = lam * star lam - 1 := by
    rw [star_sub, star_one, star_mul', star_star, mul_comm]
  set c : F := (lam * star lam - 1)⁻¹ * a with hc
  have hca : c + star c = 0 := by
    have hsc : star c = (lam * star lam - 1)⁻¹ * star a := by
      rw [hc, star_mul', star_inv₀, hDfix]
    rw [hsc, hc, ← mul_add, ha, mul_zero]
  have hgu : (uScale v w lam) ∈ Matrix.unitaryGroup N F :=
    uScale_mem v w lam hlam hvw hwv hviso hwiso
  set g : Matrix.specialUnitaryGroup N F :=
    ⟨uScale v w lam, uScale_mem_su v w lam hlam hfix hvw hwv hviso hwiso⟩ with hg
  have hgv : (g : Matrix N N F) *ᵥ v = lam • v := uScale_mulVec_self v w lam hwv hviso
  have hgcoe : (g : Matrix N N F) = uScale v w lam := rfl
  have hginv : ((g⁻¹ : Matrix.specialUnitaryGroup N F) : Matrix N N F) = (g : Matrix N N F)⁻¹ := by
    rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, Matrix.star_eq_conjTranspose]
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hgu
  have hhinv : ((uTransvecSU v c hviso hca)⁻¹ : Matrix.specialUnitaryGroup N F).1
      = (uTransvection v c)⁻¹ := by
    rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, uTransvecSU_coe,
      uTransvection_star, uTransvection_inv_eq hviso]
    congr 1
    exact eq_neg_of_add_eq_zero_right hca
  have hcomm : ⁅g, uTransvecSU v c hviso hca⁆ = uTransvecSU v a hviso ha := by
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Submonoid.coe_mul, hginv, hhinv, uTransvecSU_coe, hgcoe]
    rw [uTransvection_commutator hgu hgv hviso]
    congr 1
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top _)

open scoped commutatorElement in
/-- **`SU_n(F)` is perfect, modulo generation.** If the unitary transvections generate `SU_n(F)`
(the unitary Witt theorem — Step 3a), `F` has a fixed-field scalar `λ` with `N(λ) ≠ 1`, and every
nonzero isotropic vector has a hyperbolic partner (`exists_hyperbolic_partner`), then
`commutator (SU_n(F)) = ⊤`. Each generating transvection lies in the commutator subgroup
(`uTransvecSU_mem_commutator`; the degenerate `v = 0` transvection is the identity). The unitary
analogue of `SpN.commutator_Sp_eq_top`; the only outstanding input is the generation hypothesis. -/
theorem commutator_specialUnitaryGroup_eq_top
    (lam : F) (hlam : lam ≠ 0) (hfix : star lam = lam) (hN : lam * star lam ≠ 1)
    (hpartner : ∀ v : N → F, v ≠ 0 → star v ⬝ᵥ v = 0 →
      ∃ w : N → F, star w ⬝ᵥ w = 0 ∧ star v ⬝ᵥ w = 1)
    (hgen : Subgroup.closure {h : Matrix.specialUnitaryGroup N F |
      ∃ (v : N → F) (a : F) (hv : star v ⬝ᵥ v = 0) (ha : a + star a = 0),
        h = uTransvecSU v a hv ha} = ⊤) :
    commutator (Matrix.specialUnitaryGroup N F) = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro x ⟨v, a, hv, ha, rfl⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · have h1 : uTransvecSU (0 : N → F) a hv ha = 1 := by
      apply Subtype.ext
      simp [uTransvecSU_coe, uTransvection]
    rw [h1]; exact Subgroup.one_mem _
  · obtain ⟨w, hwiso, hvw⟩ := hpartner v hv0 hv
    have hwv : star w ⬝ᵥ v = 1 := by
      have hsw : star w ⬝ᵥ v = star (star v ⬝ᵥ w) := by
        simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star, mul_comm]
      rw [hsw, hvw, star_one]
    exact uTransvecSU_mem_commutator v w lam hlam hfix hN hvw hwv hv hwiso a ha

end Scaling

end FiniteSimpleGroups.PSU

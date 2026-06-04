import Mathlib
import FiniteSimpleGroups.SpIwasawa

/-!
# Symplectic short-root (Chevalley/Steinberg) commutator relations — toward `PSp` perfectness
for small fields `q ∈ {2,3}`

The former monolithic small-field axiom `PSp_perfect_small_field` (perfectness for `q ∈ {2,3}`,
`n ≥ 2`, `¬(n=2∧q=2)`) is **discharged here for `q = 3`** (and, in fact, for any field of
characteristic ≠ 2): the `λ²≠1` commutator engine is unavailable over `𝔽₃`, so perfectness comes
instead from the type-`Cₙ` **Steinberg relation** — the long-root transvection `τ_{eᵢ,·}` is the
group commutator of two short-root unipotents, with structure constant `2` (invertible iff char ≠ 2).
The only surviving residual is the genuinely char-2 case `PSp_perfect_char_two` (`q = 2`, `n ≥ 3`).

This file machine-checks the **algebraic core** (no field-size or characteristic hypothesis):
- `rootN1/rootN2/rootM` — the short-root (`εᵢ∓εⱼ`) unipotent generators and the long-root (`2εᵢ`)
  element, as `Matrix.single` (matrix-unit) combinations on the standard symplectic basis
  (`eᵢ = single (inr i)`, `fᵢ = single (inl i)`).
- the nine matrix-unit relations (`rootN1_sq`, `rootN1_mul_N2 = M`, `rootN2_mul_N1 = -M`, …),
- `unipotent_commutator` — the Heisenberg identity `(1+sN₁)(1+tN₂)(1-sN₁)(1-tN₂) = 1 + 2st·M`,
- `root_steinberg` — their assembly: `[1+s·N₁, 1+t·N₂] = 1 + 2st·M`.

**The structure constant `2`** (`N₁N₂ = M`, `N₂N₁ = -M`, so `[N₁,N₂] = 2M`) is exactly why
`Sp(4,2) ≅ S₆` (char 2) fails to be perfect while `Sp(4,3)` (char 3, `2` invertible) is perfect.

**Done this lap** (everything below `root_steinberg`): (a) symplectic membership
`1 + s·rootN1, 1 + s·rootN2 ∈ symplecticGroup` (`mem_one_add_rootN1/2`, the `gᵀJg = J`
computation); (b) the long-root identification `1 + c·rootM i = spTransvection (single (inr i)) (-c)`
(`one_add_rootM_eq_spTransvection`); (c) the seed `spTransvecSp_inr_mem_commutator` (`τ_{eᵢ,c}` is a
commutator over char ≠ 2), its `Sp`-conjugate spread `spTransvecSp_mem_commutator_char_ne_two`, and
`commutator_Sp_eq_top_char_ne_two` / `commutator_PSp_eq_top_char_ne_two`.

**Remaining:** the char-2 case `PSp_perfect_char_two` (`q = 2`, `n ≥ 3`) — short roots only, via the
rank-`≥3` relations `[x_{εᵢ-εⱼ}, x_{εⱼ±εₖ}] = x_{εᵢ±εₖ}` (the structure constant `2` vanishes, so the
two-short-root commutator above produces the *trivial* long root in char 2).
-/

open Matrix
open scoped commutatorElement
namespace FiniteSimpleGroups.SpN

variable {l : Type*} [DecidableEq l] [Fintype l] {F : Type*} [Field F]

/-- Short-root unipotent generator `N₁` for `ε_i - ε_j` (`i ≠ j`): `E_{e_i,e_j} - E_{f_j,f_i}`. -/
noncomputable def rootN1 (i j : l) : Matrix (l ⊕ l) (l ⊕ l) F :=
  Matrix.single (Sum.inr i) (Sum.inr j) 1 - Matrix.single (Sum.inl j) (Sum.inl i) 1

/-- Short-root unipotent generator `N₂` for `ε_i + ε_j` (`i ≠ j`): `E_{e_i,f_j} + E_{e_j,f_i}`. -/
noncomputable def rootN2 (i j : l) : Matrix (l ⊕ l) (l ⊕ l) F :=
  Matrix.single (Sum.inr i) (Sum.inl j) 1 + Matrix.single (Sum.inr j) (Sum.inl i) 1

/-- Long-root element `M` for `2ε_i`: `E_{e_i,f_i}`. -/
noncomputable def rootM (i : l) : Matrix (l ⊕ l) (l ⊕ l) F :=
  Matrix.single (Sum.inr i) (Sum.inl i) 1

theorem rootN1_sq (i j : l) (hij : i ≠ j) : rootN1 (F := F) i j * rootN1 i j = 0 := by
  simp [rootN1, sub_mul, mul_sub, single_mul_single_of_ne, Sum.inr.injEq, Sum.inl.injEq,
    hij, hij.symm]

theorem rootN2_sq (i j : l) : rootN2 (F := F) i j * rootN2 i j = 0 := by
  simp [rootN2, add_mul, mul_add, single_mul_single_of_ne]

theorem rootN1_mul_N2 (i j : l) (hij : i ≠ j) : rootN1 (F := F) i j * rootN2 i j = rootM i := by
  simp [rootN1, rootN2, rootM, sub_mul, mul_add, single_mul_single_same,
    single_mul_single_of_ne, Sum.inr.injEq, hij.symm]

theorem rootN2_mul_N1 (i j : l) (hij : i ≠ j) : rootN2 (F := F) i j * rootN1 i j = - rootM i := by
  simp [rootN2, rootN1, rootM, add_mul, mul_sub, single_mul_single_same,
    single_mul_single_of_ne, Sum.inl.injEq, hij]

theorem rootM_sq (i : l) : rootM (F := F) i * rootM i = 0 := by
  simp [rootM, single_mul_single_of_ne]

theorem rootM_mul_N1 (i j : l) (hij : i ≠ j) : rootM (F := F) i * rootN1 i j = 0 := by
  simp [rootM, rootN1, mul_sub, single_mul_single_of_ne, Sum.inl.injEq, hij]

theorem rootN1_mul_M (i j : l) (hij : i ≠ j) : rootN1 (F := F) i j * rootM i = 0 := by
  simp [rootN1, rootM, sub_mul, single_mul_single_of_ne, Sum.inr.injEq, hij.symm]

theorem rootM_mul_N2 (i j : l) : rootM (F := F) i * rootN2 i j = 0 := by
  simp [rootM, rootN2, mul_add, single_mul_single_of_ne]

theorem rootN2_mul_M (i j : l) : rootN2 (F := F) i j * rootM i = 0 := by
  simp [rootN2, rootM, add_mul, single_mul_single_of_ne]

/-- **Unipotent (Heisenberg) commutator identity.** From the nilpotent relations,
`(1+sN₁)(1+tN₂)(1-sN₁)(1-tN₂) = 1 + 2st·M`. -/
theorem unipotent_commutator (s t : F) (N1 N2 M : Matrix (l ⊕ l) (l ⊕ l) F)
    (hN1 : N1 * N1 = 0) (hN2 : N2 * N2 = 0)
    (h12 : N1 * N2 = M) (h21 : N2 * N1 = -M)
    (hMN1 : M * N1 = 0) (hMN2 : M * N2 = 0) :
    (1 + s • N1) * (1 + t • N2) * (1 - s • N1) * (1 - t • N2) = 1 + (2 * s * t) • M := by
  have e1 : (1 + s • N1) * (1 + t • N2) * (1 - s • N1)
      = 1 + t • N2 + (2 * (s * t)) • M := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, hN1, h12, h21, hMN1]
    simp only [smul_zero]
    module
  rw [e1]
  simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hN2, hMN2]
  simp only [smul_zero]
  module

/-- **Symplectic Steinberg (Chevalley) commutator relation.** For `i ≠ j`, the group commutator
of the short-root unipotents `1 + s·N₁` (root `εᵢ-εⱼ`) and `1 + t·N₂` (root `εᵢ+εⱼ`) is the
long-root element `1 + 2st·M` (root `2εᵢ`). The structure constant `2` is the obstruction in
characteristic 2 (`Sp(4,2) ≅ S₆` not perfect) and the engine of perfectness in characteristic 3. -/
theorem root_steinberg (s t : F) {i j : l} (hij : i ≠ j) :
    (1 + s • rootN1 (F := F) i j) * (1 + t • rootN2 i j) * (1 - s • rootN1 i j)
        * (1 - t • rootN2 i j)
      = 1 + (2 * s * t) • rootM i :=
  unipotent_commutator s t (rootN1 (F := F) i j) (rootN2 i j) (rootM i) (rootN1_sq i j hij)
    (rootN2_sq i j) (rootN1_mul_N2 i j hij) (rootN2_mul_N1 i j hij) (rootM_mul_N1 i j hij)
    (rootM_mul_N2 i j)

/-! ### Symplectic membership of the short-root unipotents and the perfectness assembly

The `root_steinberg` relation above is purely algebraic. To turn it into a *group* commutator we
need the short-root unipotents `1 ± s·N₁`, `1 ± t·N₂` to be **symplectic**, plus the long-root
identification `1 + c·M = τ_{eᵢ,-c}`. From these, in characteristic ≠ 2 (so `2` is invertible),
every long-root transvection at `eᵢ` is the commutator `⁅1+s·N₁, 1+N₂⁆`, hence — by `Sp`-conjugacy
of transvections — *every* transvection lies in `[Sp,Sp]`, giving `commutator(Sp) = ⊤` and (after
descending) `commutator(PSp) = ⊤`. This discharges perfectness for `q = 3`. -/

/-- generic: `1 + s•N ∈ Sp` from the two Lie-algebra identities. -/
theorem mem_one_add_smul {N : Matrix (l ⊕ l) (l ⊕ l) F} (s : F)
    (h1 : N * Matrix.J l F + Matrix.J l F * Nᵀ = 0)
    (h2 : N * Matrix.J l F * Nᵀ = 0) :
    (1 + s • N) ∈ symplecticGroup l F := by
  rw [SymplecticGroup.mem_iff]
  have ht : (1 + s • N)ᵀ = 1 + s • Nᵀ := by
    rw [transpose_add, transpose_one, transpose_smul]
  rw [ht]
  have hexp : (1 + s • N) * Matrix.J l F * (1 + s • Nᵀ)
      = Matrix.J l F + s • (N * Matrix.J l F + Matrix.J l F * Nᵀ)
        + (s * s) • (N * Matrix.J l F * Nᵀ) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_add]
    abel
  rw [hexp, h1, h2, smul_zero, smul_zero, add_zero, add_zero]

/-- `(eⱼ) ᵥ* J = fⱼ`. -/
theorem vecMul_J_inr (j : l) :
    (Pi.single (Sum.inr j) (1 : F)) ᵥ* (Matrix.J l F) = Pi.single (Sum.inl j) 1 := by
  rw [← mulVec_transpose, J_transpose, neg_mulVec, J_mulVec_single_inr, neg_neg]

/-- `(fᵢ) ᵥ* J = -eᵢ`. -/
theorem vecMul_J_inl (i : l) :
    (Pi.single (Sum.inl i) (1 : F)) ᵥ* (Matrix.J l F) = -(Pi.single (Sum.inr i) 1) := by
  rw [← mulVec_transpose, J_transpose, neg_mulVec, J_mulVec_single_inl]

omit [Fintype l] in
theorem rootN1_transpose (i j : l) :
    (rootN1 (F := F) i j)ᵀ
      = vecMulVec (Pi.single (Sum.inr j) 1) (Pi.single (Sum.inr i) 1)
        - vecMulVec (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) := by
  rw [rootN1, transpose_sub, transpose_single, transpose_single,
    single_eq_single_vecMulVec_single, single_eq_single_vecMulVec_single]

omit [Fintype l] in
theorem rootN2_transpose (i j : l) :
    (rootN2 (F := F) i j)ᵀ
      = vecMulVec (Pi.single (Sum.inl j) 1) (Pi.single (Sum.inr i) 1)
        + vecMulVec (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) := by
  rw [rootN2, transpose_add, transpose_single, transpose_single,
    single_eq_single_vecMulVec_single, single_eq_single_vecMulVec_single]

theorem rootN1_mul_J (i j : l) :
    rootN1 (F := F) i j * Matrix.J l F
      = vecMulVec (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inl j) 1)
        + vecMulVec (Pi.single (Sum.inl j) 1) (Pi.single (Sum.inr i) 1) := by
  rw [rootN1, single_eq_single_vecMulVec_single, single_eq_single_vecMulVec_single, sub_mul,
    vecMulVec_mul, vecMulVec_mul, vecMul_J_inr, vecMul_J_inl, vecMulVec_neg, sub_neg_eq_add]

theorem J_mul_rootN1_transpose (i j : l) :
    Matrix.J l F * (rootN1 (F := F) i j)ᵀ
      = -vecMulVec (Pi.single (Sum.inl j) 1) (Pi.single (Sum.inr i) 1)
        - vecMulVec (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inl j) 1) := by
  rw [rootN1_transpose, mul_sub, mul_vecMulVec, mul_vecMulVec, J_mulVec_single_inr,
    J_mulVec_single_inl, neg_vecMulVec]

theorem rootN2_mul_J (i j : l) :
    rootN2 (F := F) i j * Matrix.J l F
      = -vecMulVec (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1)
        - vecMulVec (Pi.single (Sum.inr j) 1) (Pi.single (Sum.inr i) 1) := by
  rw [rootN2, single_eq_single_vecMulVec_single, single_eq_single_vecMulVec_single, add_mul,
    vecMulVec_mul, vecMulVec_mul, vecMul_J_inl, vecMul_J_inl, vecMulVec_neg, vecMulVec_neg]
  abel

theorem J_mul_rootN2_transpose (i j : l) :
    Matrix.J l F * (rootN2 (F := F) i j)ᵀ
      = vecMulVec (Pi.single (Sum.inr j) 1) (Pi.single (Sum.inr i) 1)
        + vecMulVec (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1) := by
  rw [rootN2_transpose, mul_add, mul_vecMulVec, mul_vecMulVec, J_mulVec_single_inl,
    J_mulVec_single_inl]

theorem rootN1_mul_J_add (i j : l) :
    rootN1 (F := F) i j * Matrix.J l F + Matrix.J l F * (rootN1 i j)ᵀ = 0 := by
  rw [rootN1_mul_J, J_mul_rootN1_transpose]; abel

theorem rootN2_mul_J_add (i j : l) :
    rootN2 (F := F) i j * Matrix.J l F + Matrix.J l F * (rootN2 i j)ᵀ = 0 := by
  rw [rootN2_mul_J, J_mul_rootN2_transpose]; abel

theorem rootN1_mul_J_mul (i j : l) (hij : i ≠ j) :
    rootN1 (F := F) i j * Matrix.J l F * (rootN1 i j)ᵀ = 0 := by
  rw [rootN1_mul_J, rootN1_transpose]
  have d1 : (Pi.single (Sum.inl j) (1:F)) ⬝ᵥ (Pi.single (Sum.inr j) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp
  have d2 : (Pi.single (Sum.inl j) (1:F)) ⬝ᵥ (Pi.single (Sum.inl i : l ⊕ l) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp [hij.symm]
  have d3 : (Pi.single (Sum.inr i) (1:F)) ⬝ᵥ (Pi.single (Sum.inr j : l ⊕ l) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp [hij]
  have d4 : (Pi.single (Sum.inr i) (1:F)) ⬝ᵥ (Pi.single (Sum.inl i) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp
  simp only [add_mul, mul_sub, vecMulVec_mul_vecMulVec, d1, d2, d3, d4, zero_smul,
    vecMulVec_zero, sub_self, add_zero]

theorem rootN2_mul_J_mul (i j : l) :
    rootN2 (F := F) i j * Matrix.J l F * (rootN2 i j)ᵀ = 0 := by
  rw [rootN2_mul_J, rootN2_transpose]
  have d1 : (Pi.single (Sum.inr j) (1:F)) ⬝ᵥ (Pi.single (Sum.inl j) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp
  have d2 : (Pi.single (Sum.inr j) (1:F)) ⬝ᵥ (Pi.single (Sum.inl i) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp
  have d3 : (Pi.single (Sum.inr i) (1:F)) ⬝ᵥ (Pi.single (Sum.inl j) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp
  have d4 : (Pi.single (Sum.inr i) (1:F)) ⬝ᵥ (Pi.single (Sum.inl i) 1) = (0 : F) := by
    rw [single_one_dotProduct]; simp
  simp only [sub_mul, neg_mul, mul_add, vecMulVec_mul_vecMulVec, d1, d2, d3, d4, zero_smul,
    vecMulVec_zero, neg_zero, add_zero, sub_zero]

theorem mem_one_add_rootN1 (i j : l) (hij : i ≠ j) (s : F) :
    (1 + s • rootN1 (F := F) i j) ∈ symplecticGroup l F :=
  mem_one_add_smul s (rootN1_mul_J_add i j) (rootN1_mul_J_mul i j hij)

theorem mem_one_add_rootN2 (i j : l) (s : F) :
    (1 + s • rootN2 (F := F) i j) ∈ symplecticGroup l F :=
  mem_one_add_smul s (rootN2_mul_J_add i j) (rootN2_mul_J_mul i j)

/-- The unipotents `1 ± s•N` are mutually inverse when `N² = 0`. -/
theorem inv_one_add_smul {N : Matrix (l ⊕ l) (l ⊕ l) F} (s : F) (hN : N * N = 0) :
    (1 + s • N)⁻¹ = 1 - s • N := by
  apply Matrix.inv_eq_right_inv
  have e : (s • N) * (s • N) = (s * s) • (N * N) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [add_mul, mul_sub, one_mul, mul_one, e, hN, smul_zero]
  abel

/-- **Long-root transvection identification**: `1 + c•(E_{eᵢ,fᵢ}) = τ_{eᵢ, -c}`. Since
`J·ᵥeᵢ = -fᵢ`, the rank-one term of `τ_{eᵢ,-c}` is `(-c)•(eᵢ ⊗ (-fᵢ)) = c•rootM i`. -/
theorem one_add_rootM_eq_spTransvection (i : l) (c : F) :
    (1 : Matrix (l ⊕ l) (l ⊕ l) F) + c • rootM i
      = spTransvection (Pi.single (Sum.inr i) 1) (-c) := by
  have hr : vecMulVec (Pi.single (Sum.inr i) (1 : F)) (Matrix.J l F *ᵥ Pi.single (Sum.inr i) 1)
      = - rootM i := by
    rw [J_mulVec_single_inr, vecMulVec_neg, rootM, single_eq_single_vecMulVec_single]
  rw [spTransvection, hr]
  module

/-- **Seed: the long-root transvection at `eᵢ` is a commutator** (char ≠ 2, `n ≥ 2`).
For `i ≠ j` and `2 ≠ 0`, every `τ_{eᵢ,c}` equals `⁅1+s•N₁, 1+N₂⁆` with `s = -c/2`, hence lies
in `[Sp,Sp]`. This is the Steinberg engine of perfectness over `𝔽₃`. -/
theorem spTransvecSp_inr_mem_commutator (i j : l) (hij : i ≠ j) (h2 : (2 : F) ≠ 0) (c : F) :
    spTransvecSp (Pi.single (Sum.inr i) 1) c ∈ commutator (symplecticGroup l F) := by
  set s : F := -(c / 2) with hs
  set U1 : symplecticGroup l F := ⟨1 + s • rootN1 i j, mem_one_add_rootN1 i j hij s⟩ with hU1
  set U2 : symplecticGroup l F := ⟨1 + (1 : F) • rootN2 i j, mem_one_add_rootN2 i j 1⟩ with hU2
  have hcomm : spTransvecSp (Pi.single (Sum.inr i) 1) c = ⁅U1, U2⁆ := by
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Submonoid.coe_mul, SymplecticGroup.coe_inv', spTransvecSp_coe, hU1, hU2]
    rw [inv_one_add_smul s (rootN1_sq i j hij), inv_one_add_smul 1 (rootN2_sq i j),
      root_steinberg s 1 hij, one_add_rootM_eq_spTransvection]
    congr 1
    rw [hs]
    field_simp
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top U1) (Subgroup.mem_top U2)

/-- **Every transvection lies in `[Sp,Sp]`** (char ≠ 2, rank ≥ 2): conjugating the seed
`spTransvecSp_inr_mem_commutator` (a long-root commutator at `eᵢ`) by a `g ∈ Sp` carrying
`eᵢ → v` lands `τ_{v,c}` in the (normal) commutator subgroup. -/
theorem spTransvecSp_mem_commutator_char_ne_two [Nontrivial l] (h2 : (2 : F) ≠ 0)
    {v : (l ⊕ l) → F} (hv : v ≠ 0) (c : F) :
    spTransvecSp v c ∈ commutator (symplecticGroup l F) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne l
  have he0 : (Pi.single (Sum.inr i) 1 : (l ⊕ l) → F) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inr i)
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  obtain ⟨g, _, hg⟩ := exists_sp_transvecGen_maps he0 hv
  have hconj : spTransvecSp v c = g * spTransvecSp (Pi.single (Sum.inr i) 1) c * g⁻¹ := by
    rw [spTransvecSp_conj, hg]
  rw [hconj]
  exact (Subgroup.commutator_normal ⊤ ⊤).conj_mem _
    (spTransvecSp_inr_mem_commutator i j hij h2 c) g

/-- **`Sp(2n,F)` is perfect in characteristic ≠ 2 for `n ≥ 2`** (`commutator = ⊤`). The
generating transvections (`sp_transvec_closure_eq_top`) all lie in `[Sp,Sp]` via the symplectic
Steinberg relation — covering `𝔽₃`, where the `λ²≠1` scaling engine is unavailable. -/
theorem commutator_Sp_eq_top_char_ne_two [Nontrivial l] (h2 : (2 : F) ≠ 0) :
    commutator (symplecticGroup l F) = ⊤ := by
  rw [eq_top_iff, ← sp_transvec_closure_eq_top]
  refine iSup_le fun v => ?_
  intro y hy
  rw [mem_spTransvecGroup] at hy
  obtain ⟨c, rfl⟩ := hy
  by_cases hv : v = 0
  · subst hv
    have h0 : spTransvecSp (0 : (l ⊕ l) → F) c = 1 := by
      apply Subtype.ext; simp [spTransvecSp_coe, spTransvection]
    rw [h0]; exact one_mem _
  · exact spTransvecSp_mem_commutator_char_ne_two h2 hv c

/-- **`PSp(2n,F)` is perfect in characteristic ≠ 2 for `n ≥ 2`**. Descends from
`commutator_Sp_eq_top_char_ne_two` along `Sp ↠ Sp/Z`. -/
theorem commutator_PSp_eq_top_char_ne_two [Nontrivial l] (h2 : (2 : F) ≠ 0) :
    commutator (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) = ⊤ := by
  set G := symplecticGroup l F
  let f := QuotientGroup.mk' (Subgroup.center G)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hmap : commutator (G ⧸ Subgroup.center G) = Subgroup.map f (commutator G) := by
    show ⁅(⊤ : Subgroup _), ⊤⁆ = Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [hmap, commutator_Sp_eq_top_char_ne_two h2, Subgroup.map_top_of_surjective f hf]

end FiniteSimpleGroups.SpN

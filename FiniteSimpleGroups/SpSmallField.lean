import Mathlib
import FiniteSimpleGroups.SpIwasawa

/-!
# Symplectic short-root (Chevalley/Steinberg) commutator relations — toward `PSp` perfectness
for small fields `q ∈ {2,3}`

The former monolithic small-field axiom `PSp_perfect_small_field` (perfectness for `q ∈ {2,3}`,
`n ≥ 2`, `¬(n=2∧q=2)`) is now **fully discharged** here, so `PSp_isSimpleGroup` is axiom-clean.
Two complementary type-`Cₙ` **Steinberg engines** cover every case:
* **`n = 2` (char ≠ 2, i.e. `q = 3`):** the long-root transvection `τ_{eᵢ,·}` is the single
  short-short commutator `⁅1+s·N₁, 1+N₂⁆` with structure constant `2` (invertible) — see
  `commutator_PSp_eq_top_char_ne_two`.
* **`n ≥ 3` (ANY field, char-free):** the rank-`≥3` short-root relations
  `[x_{εᵢ-εₖ}, x_{εₖ±εⱼ}] = x_{εᵢ±εⱼ}` (structure constant `1`) plus the long-root extraction
  `⁅1+N₁(i,j), 1+a·M_j⁆ = (1+a·N₂(i,j))·τ_{eᵢ,·}` put every transvection in `[Sp,Sp]` — see
  `commutator_PSp_eq_top_n3`. This is what makes `Sp(2n,2)` perfect for `n ≥ 3`, even though the
  char-2 short-short structure constant `2` vanishes.

`PSp(4,2) ≅ S₆` (`n = 2`, `q = 2`) is genuinely not perfect, correctly excluded.

This file machine-checks the **algebraic core** (no field-size or characteristic hypothesis):
- `rootN1/rootN2/rootM` — the short-root (`εᵢ∓εⱼ`) unipotent generators and the long-root (`2εᵢ`)
  element, as `Matrix.single` (matrix-unit) combinations on the standard symplectic basis
  (`eᵢ = single (inr i)`, `fᵢ = single (inl i)`).
- the nine matrix-unit relations (`rootN1_sq`, `rootN1_mul_N2 = M`, `rootN2_mul_N1 = -M`, …),
- `unipotent_commutator` — the Heisenberg identity `(1+sN₁)(1+tN₂)(1-sN₁)(1-tN₂) = 1 + 2st·M`,
- `root_steinberg` — their assembly: `[1+s·N₁, 1+t·N₂] = 1 + 2st·M`.

**The structure constant `2`** (`N₁N₂ = M`, `N₂N₁ = -M`, so `[N₁,N₂] = 2M`) is exactly why
`Sp(4,2) ≅ S₆` (char 2) fails to be perfect while `Sp(4,3)` (char 3, `2` invertible) is perfect.

Everything below `root_steinberg` is the assembly: (a) symplectic membership
`1 + s·rootN1, 1 + s·rootN2 ∈ symplecticGroup` (`mem_one_add_rootN1/2`, the `gᵀJg = J`
computation); (b) the long-root identification `1 + c·rootM i = spTransvection (single (inr i)) (-c)`
(`one_add_rootM_eq_spTransvection`); (c) the char-≠-2 seed `spTransvecSp_inr_mem_commutator` and its
`Sp`-conjugate spread to `commutator_PSp_eq_top_char_ne_two`; (d) the char-free rank-3 engine
(`group_comm_first_order`/`group_comm_second_order`, the three Steinberg relations
`rootN1_steinberg`/`rootN2_steinberg`/`rootM_steinberg`, the seed
`spTransvecSp_inr_mem_commutator_n3`, spread to `commutator_PSp_eq_top_n3`).
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

/-- **First-order group-commutator identity** for nilpotent `X, Y` with `XYX = 0`, `Y(XY) = 0`:
`(1+sX)(1+tY)(1-sX)(1-tY) = 1 + st·(XY - YX)`. The Steinberg relation whose structure constant
is `±1` (so it survives every characteristic). -/
theorem group_comm_first_order (s t : F) (X Y : Matrix (l ⊕ l) (l ⊕ l) F)
    (hX2 : X * X = 0) (hY2 : Y * Y = 0) (hXYX : X * Y * X = 0) (hXYY : X * Y * Y = 0)
    (hYXY : Y * X * Y = 0) :
    (1 + s • X) * (1 + t • Y) * (1 - s • X) * (1 - t • Y)
      = 1 + (s * t) • (X * Y - Y * X) := by
  have e1 : (1 + s • X) * (1 + t • Y) * (1 - s • X)
      = 1 + t • Y + (s * t) • (X * Y - Y * X) := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hX2, hXYX]
    simp only [smul_zero]
    module
  rw [e1]
  simp only [add_mul, mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hY2, hXYY, hYXY]
  simp only [smul_zero]
  module

/-! #### Rank-3 short-root products (the `E_{ik}E_{kj}=E_{ij}` Levi algebra) -/

/-- `N₁(i,k)·N₁(k,j) = E_{eᵢ,eⱼ}` (`i ≠ j`). -/
theorem rootN1_mul_rootN1 (i k j : l) (hij : i ≠ j) :
    rootN1 (F := F) i k * rootN1 k j = Matrix.single (Sum.inr i) (Sum.inr j) 1 := by
  simp [rootN1, sub_mul, mul_sub, single_mul_single_same, single_mul_single_of_ne, hij]

/-- `N₁(k,j)·N₁(i,k) = E_{fⱼ,fᵢ}` (`i ≠ j`). -/
theorem rootN1_mul_rootN1' (i k j : l) (hij : i ≠ j) :
    rootN1 (F := F) k j * rootN1 i k = Matrix.single (Sum.inl j) (Sum.inl i) 1 := by
  simp [rootN1, sub_mul, mul_sub, single_mul_single_same, single_mul_single_of_ne, hij.symm]

/-- `N₁(i,k)·N₂(k,j) = E_{eᵢ,fⱼ}` (`j ≠ k`). -/
theorem rootN1_mul_rootN2 (i k j : l) (hjk : j ≠ k) :
    rootN1 (F := F) i k * rootN2 k j = Matrix.single (Sum.inr i) (Sum.inl j) 1 := by
  simp [rootN1, rootN2, sub_mul, mul_add, single_mul_single_same, single_mul_single_of_ne,
    hjk.symm]

/-- `N₂(k,j)·N₁(i,k) = -E_{eⱼ,fᵢ}` (`j ≠ k`). -/
theorem rootN2_mul_rootN1 (i k j : l) (hjk : j ≠ k) :
    rootN2 (F := F) k j * rootN1 i k = - Matrix.single (Sum.inr j) (Sum.inl i) 1 := by
  simp [rootN1, rootN2, add_mul, mul_sub, single_mul_single_same, single_mul_single_of_ne, hjk]

/-- **Second-order group-commutator identity** for nilpotent `X, Y` with `XYX = Q`, `QY = 0`,
`XYY = 0`, `YXY = 0`: `(1+sX)(1+aY)(1-sX)(1-aY) = 1 + sa·(XY-YX) - s²a·Q`. The second-order term
`Q` is the long-root contribution `2α+β` of the Chevalley formula. -/
theorem group_comm_second_order (s a : F) (X Y Q : Matrix (l ⊕ l) (l ⊕ l) F)
    (hX2 : X * X = 0) (hY2 : Y * Y = 0) (hXYX : X * Y * X = Q) (hXYY : X * Y * Y = 0)
    (hYXY : Y * X * Y = 0) (hQY : Q * Y = 0) :
    (1 + s • X) * (1 + a • Y) * (1 - s • X) * (1 - a • Y)
      = 1 + (s * a) • (X * Y - Y * X) - (s * s * a) • Q := by
  have e1 : (1 + s • X) * (1 + a • Y) * (1 - s • X)
      = 1 + a • Y + (s * a) • (X * Y - Y * X) - (s * s * a) • Q := by
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hX2, hXYX]
    simp only [smul_zero]
    module
  rw [e1]
  simp only [add_mul, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    hY2, hXYY, hYXY, hQY]
  simp only [smul_zero]
  module

/-! #### The three symplectic Steinberg relations (rank-3 short, and the long-root extraction) -/

/-- **Rank-3 short × short → short:** `⁅1+s·N₁(i,k), 1+t·N₁(k,j)⁆ = 1 + st·N₁(i,j)`
(`[ε_i-ε_k, ε_k-ε_j] = ε_i-ε_j`). Structure constant `1`, so it holds in every characteristic —
the engine that makes `Sp(2n,2)` perfect for `n ≥ 3`. -/
theorem rootN1_steinberg (s t : F) {i j k : l} (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) :
    (1 + s • rootN1 (F := F) i k) * (1 + t • rootN1 k j) * (1 - s • rootN1 i k)
        * (1 - t • rootN1 k j)
      = 1 + (s * t) • rootN1 i j := by
  have hXYX : rootN1 (F := F) i k * rootN1 k j * rootN1 i k = 0 := by
    rw [rootN1_mul_rootN1 i k j hij]
    simp [rootN1, mul_sub, single_mul_single_of_ne, hij.symm]
  have hXYY : rootN1 (F := F) i k * rootN1 k j * rootN1 k j = 0 := by
    rw [mul_assoc, rootN1_sq k j hkj, mul_zero]
  have hYXY : rootN1 (F := F) k j * rootN1 i k * rootN1 k j = 0 := by
    rw [rootN1_mul_rootN1' i k j hij]
    simp [rootN1, mul_sub, single_mul_single_of_ne, hij]
  have hbr : rootN1 (F := F) i k * rootN1 k j - rootN1 k j * rootN1 i k = rootN1 i j := by
    rw [rootN1_mul_rootN1 i k j hij, rootN1_mul_rootN1' i k j hij]; rfl
  rw [group_comm_first_order s t _ _ (rootN1_sq i k hik) (rootN1_sq k j hkj) hXYX hXYY hYXY, hbr]

/-- **Rank-3 short × short → short:** `⁅1+s·N₁(i,k), 1+t·N₂(k,j)⁆ = 1 + st·N₂(i,j)`
(`[ε_i-ε_k, ε_k+ε_j] = ε_i+ε_j`). -/
theorem rootN2_steinberg (s t : F) {i j k : l} (hik : i ≠ k) (hjk : j ≠ k) :
    (1 + s • rootN1 (F := F) i k) * (1 + t • rootN2 k j) * (1 - s • rootN1 i k)
        * (1 - t • rootN2 k j)
      = 1 + (s * t) • rootN2 i j := by
  have hXYX : rootN1 (F := F) i k * rootN2 k j * rootN1 i k = 0 := by
    rw [rootN1_mul_rootN2 i k j hjk]
    simp [rootN1, mul_sub, single_mul_single_of_ne, hjk]
  have hXYY : rootN1 (F := F) i k * rootN2 k j * rootN2 k j = 0 := by
    rw [mul_assoc, rootN2_sq k j, mul_zero]
  have hYXY : rootN2 (F := F) k j * rootN1 i k * rootN2 k j = 0 := by
    rw [rootN2_mul_rootN1 i k j hjk]
    simp [rootN2, neg_mul, mul_add, single_mul_single_of_ne]
  have hbr : rootN1 (F := F) i k * rootN2 k j - rootN2 k j * rootN1 i k = rootN2 i j := by
    rw [rootN1_mul_rootN2 i k j hjk, rootN2_mul_rootN1 i k j hjk, sub_neg_eq_add]
    rfl
  rw [group_comm_first_order s t _ _ (rootN1_sq i k hik) (rootN2_sq k j) hXYX hXYY hYXY, hbr]

/-- **Long × short → long extraction:** `⁅1+s·N₁(i,j), 1+a·M_j⁆ = (1+sa·N₂(i,j))·(1+s²a·M_i)`.
The second-order term `s²a·M_i` is the long root `2ε_i` (the `2α+β` Chevalley term). Crucially the
structure constant of `M_i` is `1` (not `2`), so this survives characteristic 2 — the mechanism by
which the long-root transvection lands in `[Sp,Sp]` even when the short-short Steinberg constant `2`
vanishes. -/
theorem rootM_steinberg (s a : F) {i j : l} (hij : i ≠ j) :
    (1 + s • rootN1 (F := F) i j) * (1 + a • rootM j) * (1 - s • rootN1 i j) * (1 - a • rootM j)
      = (1 + (s * a) • rootN2 i j) * (1 + (s * s * a) • rootM i) := by
  have hXY : rootN1 (F := F) i j * rootM j = Matrix.single (Sum.inr i) (Sum.inl j) 1 := by
    simp [rootN1, rootM, sub_mul, single_mul_single_same, single_mul_single_of_ne]
  have hYX : rootM (F := F) j * rootN1 i j = - Matrix.single (Sum.inr j) (Sum.inl i) 1 := by
    simp [rootN1, rootM, mul_sub, single_mul_single_same, single_mul_single_of_ne]
  have hXYX : rootN1 (F := F) i j * rootM j * rootN1 i j = - rootM i := by
    rw [hXY]
    simp [rootN1, rootM, mul_sub, single_mul_single_same, single_mul_single_of_ne]
  have hXYY : rootN1 (F := F) i j * rootM j * rootM j = 0 := by
    rw [mul_assoc, rootM_sq, mul_zero]
  have hYXY : rootM (F := F) j * rootN1 i j * rootM j = 0 := by
    rw [hYX]
    simp [rootM, neg_mul, single_mul_single_of_ne]
  have hQY : (- rootM (F := F) i) * rootM j = 0 := by
    simp [rootM, neg_mul, single_mul_single_of_ne]
  have hbr : rootN1 (F := F) i j * rootM j - rootM j * rootN1 i j = rootN2 i j := by
    rw [hXY, hYX, sub_neg_eq_add]; rfl
  rw [group_comm_second_order s a _ _ _ (rootN1_sq i j hij) (rootM_sq j) hXYX hXYY hYXY hQY, hbr]
  -- 1 + sa•N₂ - (s*s*a)•(-M_i) = (1+sa•N₂)(1+s²a•M_i)
  have hexp : (1 + (s * a) • rootN2 (F := F) i j) * (1 + (s * s * a) • rootM i)
      = 1 + (s * a) • rootN2 i j + (s * s * a) • rootM i := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
      rootN2_mul_M i j, smul_zero, add_zero]
    abel
  rw [hexp, smul_neg, sub_neg_eq_add]

/-! #### Group-level assembly: perfectness of `Sp(2n,F)` for `n ≥ 3` (any field) -/

/-- `1 + a·M_j ∈ Sp` (it is the transvection `τ_{e_j,-a}`). -/
theorem mem_one_add_rootM (j : l) (a : F) :
    (1 + a • rootM j) ∈ symplecticGroup l F := by
  rw [one_add_rootM_eq_spTransvection]; exact spTransvection_mem _ _

/-- **The short-root unipotent `1 + r·N₂(i,j)` is a commutator** (given a third index `k`):
`= ⁅1+N₁(i,k), 1+r·N₂(k,j)⁆` by `rootN2_steinberg`. Needs `n ≥ 3`. -/
theorem rootN2_mem_commutator (i j k : l) (hik : i ≠ k) (hjk : j ≠ k) (r : F) :
    (⟨1 + r • rootN2 i j, mem_one_add_rootN2 i j r⟩ : symplecticGroup l F)
      ∈ commutator (symplecticGroup l F) := by
  set V1 : symplecticGroup l F := ⟨1 + (1 : F) • rootN1 i k, mem_one_add_rootN1 i k hik 1⟩ with hV1
  set V2 : symplecticGroup l F := ⟨1 + r • rootN2 k j, mem_one_add_rootN2 k j r⟩ with hV2
  have hcomm : (⟨1 + r • rootN2 i j, mem_one_add_rootN2 i j r⟩ : symplecticGroup l F) = ⁅V1, V2⁆ := by
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Submonoid.coe_mul, SymplecticGroup.coe_inv', hV1, hV2]
    rw [inv_one_add_smul 1 (rootN1_sq i k hik), inv_one_add_smul r (rootN2_sq k j),
      rootN2_steinberg (i := i) (j := j) (k := k) 1 r hik hjk, one_mul]
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top V1) (Subgroup.mem_top V2)

/-- **Seed (n ≥ 3): the long-root transvection at `e_i` is in `[Sp,Sp]` over ANY field.**
From `rootM_steinberg` (s=1, a=-c): `⁅1+N₁(i,j), 1+(-c)·M_j⁆ = (1+(-c)·N₂(i,j))·τ_{e_i,c}`. The
short-root factor is a commutator (`rootN2_mem_commutator`, needs the third index `k`), so
`τ_{e_i,c}` — being its inverse times a commutator — lies in `[Sp,Sp]`. Characteristic-free: this
is what makes `Sp(2n,2)` perfect for `n ≥ 3`. -/
theorem spTransvecSp_inr_mem_commutator_n3 (i j k : l) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (c : F) :
    spTransvecSp (Pi.single (Sum.inr i) 1) c ∈ commutator (symplecticGroup l F) := by
  set W : symplecticGroup l F := ⟨1 + (-c) • rootN2 i j, mem_one_add_rootN2 i j (-c)⟩ with hW
  set V1 : symplecticGroup l F := ⟨1 + (1 : F) • rootN1 i j, mem_one_add_rootN1 i j hij 1⟩ with hV1
  set V2 : symplecticGroup l F := ⟨1 + (-c) • rootM j, mem_one_add_rootM j (-c)⟩ with hV2
  have hWV : ⁅V1, V2⁆ = W * spTransvecSp (Pi.single (Sum.inr i) 1) c := by
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Submonoid.coe_mul, SymplecticGroup.coe_inv', spTransvecSp_coe, hW, hV1, hV2]
    rw [inv_one_add_smul 1 (rootN1_sq i j hij), inv_one_add_smul (-c) (rootM_sq j),
      rootM_steinberg (i := i) (j := j) 1 (-c) hij,
      show spTransvection (Pi.single (Sum.inr i) 1) c = 1 + (-c) • rootM i from by
        rw [one_add_rootM_eq_spTransvection, neg_neg]]
    simp only [one_mul]
  have hkey : spTransvecSp (Pi.single (Sum.inr i) 1) c = W⁻¹ * ⁅V1, V2⁆ := by
    rw [hWV, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hkey]
  exact mul_mem (inv_mem (rootN2_mem_commutator i j k hik hjk (-c)))
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top V1) (Subgroup.mem_top V2))

/-- **`Sp(2n,F)` is perfect for `n ≥ 3` over EVERY field** (`commutator = ⊤`). The transvections
generate `Sp` (`sp_transvec_closure_eq_top`) and each lies in `[Sp,Sp]`: the seed long-root
transvection at `e_{i₀}` does (`spTransvecSp_inr_mem_commutator_n3`), and `Sp`-conjugacy spreads it
to every transvection. Characteristic-free — in particular this discharges `Sp(2n,2)` perfectness. -/
theorem commutator_Sp_eq_top_n3 (hcard : 2 < Fintype.card l) :
    commutator (symplecticGroup l F) = ⊤ := by
  obtain ⟨i, j, k, hij, hik, hjk⟩ := Fintype.two_lt_card_iff.mp hcard
  have he0 : (Pi.single (Sum.inr i) 1 : (l ⊕ l) → F) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inr i)
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  have hseed : ∀ {v : (l ⊕ l) → F}, v ≠ 0 → ∀ c : F,
      spTransvecSp v c ∈ commutator (symplecticGroup l F) := by
    intro v hv c
    obtain ⟨g, _, hg⟩ := exists_sp_transvecGen_maps he0 hv
    have hconj : spTransvecSp v c = g * spTransvecSp (Pi.single (Sum.inr i) 1) c * g⁻¹ := by
      rw [spTransvecSp_conj, hg]
    rw [hconj]
    exact (Subgroup.commutator_normal ⊤ ⊤).conj_mem _
      (spTransvecSp_inr_mem_commutator_n3 i j k hij hik hjk c) g
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
  · exact hseed hv c

/-- **`PSp(2n,F)` is perfect for `n ≥ 3` over EVERY field**. Descends from `commutator_Sp_eq_top_n3`
along `Sp ↠ Sp/Z`. -/
theorem commutator_PSp_eq_top_n3 (hcard : 2 < Fintype.card l) :
    commutator (symplecticGroup l F ⧸ Subgroup.center (symplecticGroup l F)) = ⊤ := by
  set G := symplecticGroup l F
  let f := QuotientGroup.mk' (Subgroup.center G)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hmap : commutator (G ⧸ Subgroup.center G) = Subgroup.map f (commutator G) := by
    show ⁅(⊤ : Subgroup _), ⊤⁆ = Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [hmap, commutator_Sp_eq_top_n3 hcard, Subgroup.map_top_of_surjective f hf]

end FiniteSimpleGroups.SpN

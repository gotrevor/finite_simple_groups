import Mathlib
import FiniteSimpleGroups.SpIwasawa

/-!
# Symplectic short-root (Chevalley/Steinberg) commutator relations — toward `PSp` perfectness
for small fields `q ∈ {2,3}`

The sole remaining `PSp(2n,q)` axiom is `PSp_perfect_small_field` (perfectness for `q ∈ {2,3}`,
`n ≥ 2`, `¬(n=2∧q=2)`). The `λ²≠1` commutator engine fails there, so perfectness comes from the
type-`Cₙ` **Steinberg relation**: the long-root transvection `τ_{eᵢ,·}` is the group commutator of
two short-root unipotents.

This file machine-checks the **algebraic core** (no field-size or characteristic hypothesis):
- `rootN1/rootN2/rootM` — the short-root (`εᵢ∓εⱼ`) unipotent generators and the long-root (`2εᵢ`)
  element, as `Matrix.single` (matrix-unit) combinations on the standard symplectic basis
  (`eᵢ = single (inr i)`, `fᵢ = single (inl i)`).
- the nine matrix-unit relations (`rootN1_sq`, `rootN1_mul_N2 = M`, `rootN2_mul_N1 = -M`, …),
- `unipotent_commutator` — the Heisenberg identity `(1+sN₁)(1+tN₂)(1-sN₁)(1-tN₂) = 1 + 2st·M`,
- `root_steinberg` — their assembly: `[1+s·N₁, 1+t·N₂] = 1 + 2st·M`.

**The structure constant `2`** (`N₁N₂ = M`, `N₂N₁ = -M`, so `[N₁,N₂] = 2M`) is exactly why
`Sp(4,2) ≅ S₆` (char 2) fails to be perfect while `Sp(4,3)` (char 3, `2` invertible) is perfect.

**Remaining (next lap, see `PENDING_WORK.md` §F.0):** (a) symplectic membership
`1 ± s·rootN1, 1 ± s·rootN2 ∈ symplecticGroup` (the `gᵀJg = J` computation, like
`spTransvection_mem`); (b) identify `1 + c·rootM i` with the repo transvection
`spTransvection (single (inr i)) (-c)` (since `J ·ᵥ eᵢ = -fᵢ` gives
`vecMulVec eᵢ (J·eᵢ) = -rootM i`); (c) `commutator_Sp_eq_top` for `q ∈ {2,3}` (char 3: long
roots are commutators by `root_steinberg`, short roots via `[x_{2εⱼ}, x_{εᵢ-εⱼ}]`; char 2,
`n ≥ 3`: short roots only) ⇒ descend to discharge `PSp_perfect_small_field`.
-/

open Matrix
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

end FiniteSimpleGroups.SpN

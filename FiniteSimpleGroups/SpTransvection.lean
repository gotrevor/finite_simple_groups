import Mathlib

/-!
# Symplectic transvections — first brick toward `PSp_{2n}(q)` simplicity

The next classical family after `PSL` (now fully axiom-clean, see `SL2.PSL_isSimpleGroup`)
is `PSp`. `LieType.PSp n q` is the concrete group
`symplecticGroup (Fin n) (ZMod q) ⧸ center`, and `PSp_isSimpleGroup` is still an `axiom`.
Discharging it follows the same Iwasawa route as `PSL`, but on the **symplectic** geometry:
the role of the elementary transvection `transvecSL` is played by the **symplectic
transvection** `τ_{v,c}(x) = x + c·ω(x,v)·v`, where `ω(x,y) = xᵀ (J l R) y` is the standard
symplectic form (`J = [[0,-1],[1,0]]` in block form on `l ⊕ l`).

This file builds the foundation:

* `spTransvection v c` — the matrix `1 + c • (v ⊗ J·v)` of `τ_{v,c}`.
* `spTransvection_mem` — **it lies in `symplecticGroup l R`** (`M J Mᵀ = J`, for ALL `v, c`),
  the symplectic analogue of `det_transvection_of_ne`. Machine-checked, `#print axioms`-clean.

The proof rests on three identities for the canonical form matrix `J`: `Jᵀ J = 1`
(from `J_transpose`/`J_squared`), `J (J v) = -v`, and the *alternating* identity
`v ⬝ᵥ (J v) = 0` — the last proved via `J`'s block structure (NOT via skew-symmetry alone,
which would only give `2·(vᵀJv) = 0`, insufficient in characteristic 2).

**Next bricks** (see `PENDING_WORK.md §F`): symplectic transvections generate `Sp` (the
perfectness input — the analogue of `transvecSL_closure_eq_top`), then the `PSp ↷ ℙ²ⁿ⁻¹`
action / quasi-preprimitivity (NB: `Sp` is transitive but **not** 2-transitive on points —
it preserves `ω`, so the primitivity argument differs from `PSL`).
-/

open Matrix

namespace FiniteSimpleGroups.SpN

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

/-- The **symplectic transvection** `τ_{v,c}` on `R^{l⊕l}` with the standard symplectic
form `ω(x,y) = xᵀ (J l R) y`: the map `x ↦ x + c·ω(x,v)·v`, realised as the matrix
`1 + c • (v ⊗ (J·v))` (where `v ⊗ w = vecMulVec v w` is the outer product). -/
noncomputable def spTransvection (v : (l ⊕ l) → R) (c : R) :
    Matrix (l ⊕ l) (l ⊕ l) R :=
  1 + c • Matrix.vecMulVec v ((Matrix.J l R).mulVec v)

/-- **A symplectic transvection lies in the symplectic group** (for every `v` and `c`):
`M (J) Mᵀ = J`. The symplectic analogue of `det_transvection_of_ne` for `SL`. The two cross
terms cancel (`J Nᵀ = -(N J)`) and the quadratic term vanishes by the alternating identity
`v ⬝ᵥ (J v) = 0`. -/
theorem spTransvection_mem (v : (l ⊕ l) → R) (c : R) :
    spTransvection v c ∈ symplecticGroup l R := by
  rw [SymplecticGroup.mem_iff]
  set Jm := Matrix.J l R with hJm
  set N : Matrix (l ⊕ l) (l ⊕ l) R := vecMulVec v (Jm *ᵥ v) with hN
  have hJsq : Jm * Jm = -1 := by rw [hJm]; exact J_squared l R
  have hJt : Jmᵀ = -Jm := by rw [hJm]; exact J_transpose l R
  have hNt : Nᵀ = vecMulVec (Jm *ᵥ v) v := by rw [hN, transpose_vecMulVec]
  have hJJ : Jmᵀ * Jm = 1 := by rw [hJt, neg_mul, hJsq]; exact neg_neg _
  have hJ2v : Jm *ᵥ (Jm *ᵥ v) = -v := by
    rw [mulVec_mulVec, hJsq, neg_mulVec, one_mulVec]
  -- the alternating identity, proved via the block structure of `J`
  have hskew : v ⬝ᵥ (Jm *ᵥ v) = 0 := by
    have hblk : Jm = Matrix.fromBlocks 0 (-1) 1 0 := rfl
    rw [hblk, fromBlocks_mulVec]
    simp only [zero_mulVec, one_mulVec, neg_mulVec, zero_add, add_zero]
    nth_rewrite 1 [← Sum.elim_comp_inl_inr v]
    rw [sumElim_dotProduct_sumElim, dotProduct_neg,
      dotProduct_comm (v ∘ Sum.inr) (v ∘ Sum.inl)]
    ring
  have hNJ : N * Jm = vecMulVec v v := by
    rw [hN, vecMulVec_mul, vecMul_mulVec, hJJ, vecMul_one]
  have hJNt : Jm * Nᵀ = -(vecMulVec v v) := by
    rw [hNt, mul_vecMulVec, hJ2v, neg_vecMulVec]
  have hNJNt : N * Jm * Nᵀ = 0 := by
    rw [hNJ, hNt, vecMulVec_mul_vecMulVec, hskew, zero_smul, vecMulVec_zero]
  show (1 + c • N) * Jm * (1 + c • N)ᵀ = Jm
  rw [transpose_add, transpose_one, transpose_smul]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  rw [hNJNt, hJNt, hNJ]
  simp [smul_neg]

/-- The symplectic transvection packaged as an element of `symplecticGroup l R`. -/
noncomputable def spTransvecSp (v : (l ⊕ l) → R) (c : R) : symplecticGroup l R :=
  ⟨spTransvection v c, spTransvection_mem v c⟩

end FiniteSimpleGroups.SpN

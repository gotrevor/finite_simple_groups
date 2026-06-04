import Mathlib

/-!
# The linear action of `Sp(2n,F)` on `(l⊕l) → F`, and the induced action on `ℙ²ⁿ⁻¹`

The symplectic Iwasawa route to `PSp(2n,q)` simplicity needs the action of
`PSp(2n,q)` on the projective space `ℙ²ⁿ⁻¹(F_q) = Projectivization F ((l⊕l) → F)`.
Its foundation is the **linear** action of the symplectic group `symplecticGroup l F`
on `(l⊕l) → F` by matrix-vector product (`mulVec`), which — being linear and
commuting with scalars — feeds mathlib's `MulAction G (ℙ K V)` instance
(`LinearAlgebra/Projectivization/Action.lean`, requiring `Group G`,
`DistribMulAction G V`, `SMulCommClass G K V`) to yield an action on `ℙ²ⁿ⁻¹`.

This mirrors `SLnAction.lean` (the `SL`/`PSL` thread) for the symplectic group.
The descent to `PSp = Sp/center` lives with the `PSp` Iwasawa thread.
-/

open Matrix

namespace FiniteSimpleGroups.SpN

variable {l : Type*} [DecidableEq l] [Fintype l] {F : Type*} [Field F]

/-- `Sp(2n,F)` acts on the vector space `(l⊕l) → F` by matrix-vector product. -/
instance : SMul (symplecticGroup l F) ((l ⊕ l) → F) where
  smul g v := (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v

@[simp] theorem smul_vec_def (g : symplecticGroup l F) (v : (l ⊕ l) → F) :
    g • v = (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v := rfl

instance : MulAction (symplecticGroup l F) ((l ⊕ l) → F) where
  one_smul v := by
    show ((1 : symplecticGroup l F) : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v = v
    simp
  mul_smul g h v := by
    show ((g * h : symplecticGroup l F) : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v
        = (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec
            ((h : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v)
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

instance : DistribMulAction (symplecticGroup l F) ((l ⊕ l) → F) where
  smul_zero g := by
    show (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec 0 = 0; simp
  smul_add g v w := by
    show (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec (v + w)
        = (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v
          + (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec w
    simp [Matrix.mulVec_add]

instance : SMulCommClass (symplecticGroup l F) F ((l ⊕ l) → F) where
  smul_comm g c v := by
    show (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec (c • v)
        = c • (g : Matrix (l ⊕ l) (l ⊕ l) F).mulVec v
    simp [Matrix.mulVec_smul]

/-- **`Sp(2n,F)` acts on the projective space `ℙ²ⁿ⁻¹(F)`** (via mathlib's projective-space
action instance, fed by the linear `mulVec` action above). `PSp(2n,q)` descends through the
center (in the Iwasawa thread). -/
example : MulAction (symplecticGroup l F) (Projectivization F ((l ⊕ l) → F)) :=
  inferInstance

end FiniteSimpleGroups.SpN

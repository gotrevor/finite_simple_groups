import Mathlib

/-!
# The linear action of `SL(n,F)` on `n → F`, and the induced action on `ℙ^{n-1}`

The Iwasawa route to `PSL(n,q)` simplicity (`PSL_isSimpleGroup_rank_ge_three`)
needs the action of `PSL(n,q)` on `ℙ^{n-1}(F_q) = Projectivization F (n → F)`.
Its foundation is the **linear** action of `SL(n,F)` on `n → F` by matrix-vector
product (`mulVec`), which — being linear and commuting with scalars — feeds
mathlib's `MulAction G (ℙ K V)` instance
(`LinearAlgebra/Projectivization/Action.lean`) to yield an action on `ℙ^{n-1}`.

This file declares those linear-action instances **once, for general `n`**, so
that both `SL2.lean` (the `n = 2`/`ℙ¹` thread) and the `n ≥ 3` thread reuse them
without declaring conflicting `Fin 2`-specialised copies (which would create
instance diamonds at `n = Fin 2`). The descent to `PSL = SL/center` lives with
each thread.
-/

open Matrix

namespace FiniteSimpleGroups.SLn

variable {n : Type*} [DecidableEq n] [Fintype n] {F : Type*} [Field F]

/-- `SL(n,F)` acts on the vector space `n → F` by matrix-vector product. -/
instance : SMul (SpecialLinearGroup n F) (n → F) where
  smul g v := g.val.mulVec v

@[simp] theorem smul_vec_def (g : SpecialLinearGroup n F) (v : n → F) :
    g • v = g.val.mulVec v := rfl

instance : MulAction (SpecialLinearGroup n F) (n → F) where
  one_smul v := by show (1 : SpecialLinearGroup n F).val.mulVec v = v; simp
  mul_smul g h v := by
    change (g.val * h.val).mulVec v = g.val.mulVec (h.val.mulVec v)
    rw [← Matrix.mulVec_mulVec]

instance : DistribMulAction (SpecialLinearGroup n F) (n → F) where
  smul_zero g := by show g.val.mulVec 0 = 0; simp
  smul_add g v w := by
    show g.val.mulVec (v + w) = g.val.mulVec v + g.val.mulVec w
    simp [Matrix.mulVec_add]

instance : SMulCommClass (SpecialLinearGroup n F) F (n → F) where
  smul_comm g c v := by
    show g.val.mulVec (c • v) = c • g.val.mulVec v
    simp [Matrix.mulVec_smul]

/-- **`SL(n,F)` acts on the projective space `ℙ^{n-1}(F)`** (via mathlib's
projective-space action instance, fed by the linear `mulVec` action above). The
quotient action of `PSL(n,q)` descends through the center (each thread). -/
example : MulAction (SpecialLinearGroup n F) (Projectivization F (n → F)) :=
  inferInstance

end FiniteSimpleGroups.SLn

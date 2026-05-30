import Mathlib
import FiniteSimpleGroups.LieType

/-!
# PSL via the Iwasawa criterion — the first opaque carrier turned real

`Classification.lean` carries the simplicity of `PSL n q` as an `axiom`
(`PSL_isSimpleGroup`). This file begins discharging it for `PSL 2 q` using
mathlib's **Iwasawa criterion** (`MulAction.IwasawaStructure.isSimpleGroup`,
`Mathlib/GroupTheory/GroupAction/Iwasawa.lean`).

## The criterion (mathlib's exact interface)

`MulAction.IwasawaStructure.isSimpleGroup` proves `IsSimpleGroup M` from:

1. `[Nontrivial M]`,
2. `is_perfect : commutator M = ⊤`  (M is perfect),
3. `[IsQuasiPreprimitive M α]`  (the action is quasi-preprimitive),
4. `IwaS : IwasawaStructure M α`  (a family `T : α → Subgroup M` of *abelian*
   subgroups, conjugation-equivariant, with `iSup T = ⊤`),
5. `is_faithful : FaithfulSMul M α`.

## This file's contribution (sorry-free)

`PSL2_isSimpleGroup_of_iwasawa` **wires our carrier `PSL 2 q` to mathlib's
criterion**: given the five obligations for the action on a type `α`, it
concludes `IsSimpleGroup (PSL 2 q)`. This is a real reduction — no `sorry`,
no new axiom — turning "prove PSL simple" into five concrete sub-goals.

## The roadmap (remaining work, multi-session)

Take `α = ℙ¹(F_q)` (the projective line), `M = PSL 2 q` acting by Möbius maps.

| Obligation | Plan | mathlib hooks |
|---|---|---|
| `MulAction (PSL 2 q) α` | Möbius action of `PGL₂`/`PSL₂` on `Projectivization` | `Projectivization`, `Matrix.GeneralLinearGroup` action on lines |
| `Nontrivial (PSL 2 q)` | order `q(q²−1)/gcd(2,q−1) > 1` for `q ≥ 4` | cardinality of `SL₂` / center |
| `commutator = ⊤` (perfect) | `PSL₂(q)` perfect for `q ≥ 4` | generation by transvections; `commutator` API |
| `IsQuasiPreprimitive` | `PSL₂` is 2-transitive on `ℙ¹`, hence primitive | `IsPreprimitive` / 2-transitivity lemmas |
| `IwasawaStructure` | `T(line)` = unipotent radical fixing that point (an abelian `F_q⁺`), conjugation-equivariant, generating | `Subgroup`, `MulAut.conj`, `iSup` |
| `FaithfulSMul` | only the identity fixes every point of `ℙ¹` | faithfulness of the projective action |

`q` is taken prime (so `ZMod q` is the field `F_q`); prime-power `q` needs
`GaloisField p k` in place of `ZMod q` (the same caveat flagged in `LieType`).
-/

namespace FiniteSimpleGroups

open MulAction

/-- **PSL(2,q) is simple, reduced to the five Iwasawa obligations.** Given an
action of `PSL 2 q` on a type `α` that is nontrivial, perfect, quasi-
preprimitive, faithful, and carries an Iwasawa structure, `PSL 2 q` is simple.

This discharges `PSL_isSimpleGroup` for `n = 2` *modulo* constructing the
projective-line action and verifying the five hypotheses (see the roadmap
above). It is sorry-free: the reduction itself is complete. -/
theorem PSL2_isSimpleGroup_of_iwasawa
    (q : ℕ) {α : Type*} [MulAction (PSL 2 q) α]
    [Nontrivial (PSL 2 q)] [IsQuasiPreprimitive (PSL 2 q) α]
    (perfect : commutator (PSL 2 q) = ⊤)
    (iwa : IwasawaStructure (PSL 2 q) α)
    (faithful : FaithfulSMul (PSL 2 q) α) :
    IsSimpleGroup (PSL 2 q) :=
  iwa.isSimpleGroup perfect faithful

end FiniteSimpleGroups

import Mathlib
import FiniteSimpleGroups.LieType
import FiniteSimpleGroups.SpIwasawa

/-!
# Wiring `PSp(2n,q)` simplicity into the LieType axiom

This file discharges the former monolithic LieType `axiom PSp_isSimpleGroup` into a **theorem**,
mirroring the `PSL_isSimpleGroup` discharge (in `SL2.lean`).

`PSp n q = symplecticGroup (Fin n) (ZMod q) ⧸ center`. For `q ≥ 5` (prime), `PSp(2n,q)` simplicity
is the machine-checked symplectic Iwasawa criterion `SpN.PSpn_isSimpleGroup_of_iwasawa`, which after
this lap rests on the **single** geometric axiom `SpN.sp_stab_transitive_on_perp_lines` (the Δ₀
perp-line Witt transitivity). For `q ∈ {2,3}` the `λ²≠1` route is unavailable (those fields have no
such scalar), so a `PSp_isSimpleGroup_small_field` residual covers them.

**Soundness fix.** The old `axiom PSp_isSimpleGroup (n q) (2≤n) (¬(n=2∧q=2))` was unsound for
composite `q` (`ZMod q` is a field only for prime `q`; e.g. `PSp(2n, ZMod 6)` is not simple). The
theorem here carries `[Fact (Nat.Prime q)]`, exactly as the PSL fix did.
-/

open Matrix

namespace FiniteSimpleGroups

/-- For a prime `q > 3`, `ZMod q` has a scalar `λ ≠ 0` with `λ² ≠ 1` — take `λ = 2`
(`2 ≠ 0` and `4 ≠ 1` since `q ∤ 2` and `q ∤ 3`). The honest `|F| ≥ 4` hypothesis of the
symplectic Iwasawa criterion. -/
theorem exists_sq_ne_one (q : ℕ) [Fact (Nat.Prime q)] (hq : 3 < q) :
    ∃ lam : ZMod q, lam ≠ 0 ∧ lam * lam ≠ 1 := by
  refine ⟨2, ?_, ?_⟩
  · have h2 : ((2 : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod q) q]
      intro h; exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    simpa using h2
  · have h3 : ((3 : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod q) q]
      intro h; exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    intro hc
    apply h3
    have h30 : (3 : ZMod q) = 0 := by linear_combination hc
    simpa using h30

/-- **Residual axiom for small fields `q ∈ {2,3}`.** `PSp(2n,q)` is simple for prime `q ∈ {2,3}`
(excluding the non-simple `PSp(4,2) ≅ S₆`). The Iwasawa route used for `q ≥ 5` needs a scalar
`λ ≠ 0`, `λ² ≠ 1` (i.e. `|F| ≥ 4`), which `ZMod 2`, `ZMod 3` lack; perfectness for these small
fields needs a separate commutator argument. Mirrors the `q ∈ {2,3}` gap in the PSL thread. -/
axiom PSp_isSimpleGroup_small_field (n q : ℕ) [Fact (Nat.Prime q)]
    (h_n : 2 ≤ n) (hq : q ≤ 3) (h_skip : ¬ (n = 2 ∧ q = 2)) :
    IsSimpleGroup (PSp n q)

/-- **`PSp(2n,q)` is simple** for `2 ≤ n`, prime `q`, excluding `PSp(4,2) ≅ S₆` (`h_skip`).
Discharges the former monolithic LieType axiom `PSp_isSimpleGroup`.

* `q ≥ 5`: the machine-checked symplectic Iwasawa criterion `SpN.PSpn_isSimpleGroup_of_iwasawa`,
  resting (this lap) on the single geometric axiom `SpN.sp_stab_transitive_on_perp_lines`.
* `q ∈ {2,3}`: the `PSp_isSimpleGroup_small_field` residual.

`#print axioms PSp_isSimpleGroup` =
`[propext, Classical.choice, Quot.sound, SpN.sp_stab_transitive_on_perp_lines,
PSp_isSimpleGroup_small_field]` — the deep family axiom is replaced by the perp-line Witt
transitivity and the small-field residual. -/
theorem PSp_isSimpleGroup (n q : ℕ) [Fact (Nat.Prime q)]
    (h_n : 2 ≤ n) (h_skip : ¬ (n = 2 ∧ q = 2)) :
    IsSimpleGroup (PSp n q) := by
  rcases lt_or_ge q 4 with hq | hq
  · exact PSp_isSimpleGroup_small_field n q h_n (by omega) h_skip
  · haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact SpN.PSpn_isSimpleGroup_of_iwasawa (l := Fin n) (F := ZMod q)
      (exists_sq_ne_one q (by omega))

end FiniteSimpleGroups

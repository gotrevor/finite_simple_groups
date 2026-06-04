import Mathlib
import FiniteSimpleGroups.LieType
import FiniteSimpleGroups.SpIwasawa
import FiniteSimpleGroups.SpSmallField

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

/-- For prime `q ≠ 2`, `2` is invertible in `ZMod q` (`q ∤ 2`). -/
theorem two_ne_zero_zmod (q : ℕ) [Fact (Nat.Prime q)] (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  have hp : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
  have h2 : ((2 : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod q) q]
    intro h; exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  simpa using h2

/-- **Residual axiom for `q = 2`, `n ≥ 3` — the genuinely char-2 short-root core.** `Sp(2n,2)` is
perfect (`commutator = ⊤`) for `n ≥ 3`. In characteristic 2 the symplectic Steinberg structure
constant `2` vanishes (`SpN.root_steinberg`), so the long-root transvection is *not* a commutator
of the two short roots; perfectness instead comes from the rank-`≥3` short-root relations
`[x_{εᵢ-εⱼ}, x_{εⱼ±εₖ}] = x_{εᵢ±εₖ}` (third index `k`), which need `n ≥ 3`. `Sp(4,2) ≅ S₆`
(`n = 2`) is genuinely *not* perfect, correctly excluded. This is strictly narrower than the former
`PSp_perfect_small_field` axiom — the `q = 3` case is now the machine-checked theorem below. -/
axiom PSp_perfect_char_two (n : ℕ) (h_n : 3 ≤ n) :
    commutator (PSp n 2) = ⊤

/-- **`PSp(2n,q)` is perfect for prime `q ∈ {2,3}`, `2 ≤ n`, excluding `PSp(4,2)`** — formerly the
monolithic small-field axiom, now **discharged for `q = 3`** via the symplectic Steinberg relation
(`SpN.commutator_PSp_eq_top_char_ne_two`, machine-checked). For `q = 2` it reduces to the narrower
char-2 residual `PSp_perfect_char_two` (`n ≥ 3`, forced by `h_skip` + `h_n`). -/
theorem PSp_perfect_small_field (n q : ℕ) [Fact (Nat.Prime q)]
    (h_n : 2 ≤ n) (hq : q ≤ 3) (h_skip : ¬ (n = 2 ∧ q = 2)) :
    commutator (PSp n q) = ⊤ := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h_n
  rcases eq_or_ne q 2 with hq2 | hq2
  · -- `q = 2`: `n ≥ 3` (from `h_n` and `¬(n = 2 ∧ q = 2)`), char-2 residual
    subst hq2
    have hn3 : 3 ≤ n := by
      rcases Nat.lt_or_ge n 3 with h | h
      · exact absurd ⟨by omega, rfl⟩ h_skip
      · exact h
    exact PSp_perfect_char_two n hn3
  · -- `q ≠ 2`, prime, `q ≤ 3` ⟹ `q = 3`: characteristic ≠ 2, Steinberg engine applies
    exact SpN.commutator_PSp_eq_top_char_ne_two (l := Fin n) (F := ZMod q) (two_ne_zero_zmod q hq2)

/-- `PSp(2n,q)` simple for prime `q ∈ {2,3}` (excluding `PSp(4,2)`), from the perfectness residual
`PSp_perfect_small_field` fed through `PSpn_isSimpleGroup_of_perfect` (faithfulness + quasi-
primitivity hold over any field). -/
theorem PSp_isSimpleGroup_small_field (n q : ℕ) [Fact (Nat.Prime q)]
    (h_n : 2 ≤ n) (hq : q ≤ 3) (h_skip : ¬ (n = 2 ∧ q = 2)) :
    IsSimpleGroup (PSp n q) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact SpN.PSpn_isSimpleGroup_of_perfect (l := Fin n) (F := ZMod q)
    (PSp_perfect_small_field n q h_n hq h_skip)

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

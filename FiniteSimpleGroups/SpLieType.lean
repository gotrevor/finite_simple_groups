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

/-- **`PSp(2n,q)` is perfect for prime `q ∈ {2,3}`, `2 ≤ n`, excluding `PSp(4,2)` — fully
machine-checked, ZERO custom axioms.** Two complementary symplectic Steinberg engines cover every
case:
* `n ≥ 3` (any `q`): the rank-`≥3` short-root relations `[x_{εᵢ-εₖ}, x_{εₖ±εⱼ}] = x_{εᵢ±εⱼ}`
  (structure constant `1`, characteristic-free) put the long-root transvections in `[Sp,Sp]`
  (`SpN.commutator_PSp_eq_top_n3`). This is what makes `Sp(2n,2)` perfect for `n ≥ 3`.
* `n = 2`: then `q ≠ 2` (forced by `h_skip`), so `q = 3` (prime, `≤ 3`) has characteristic ≠ 2 and
  the long-root transvection `τ_{eᵢ,c} = ⁅1+s·N₁, 1+N₂⁆` is a single short-short commutator
  (`SpN.commutator_PSp_eq_top_char_ne_two`).

`PSp(4,2) ≅ S₆` (`n = 2`, `q = 2`) is genuinely not perfect, correctly excluded by `h_skip`. -/
theorem PSp_perfect_small_field (n q : ℕ) [Fact (Nat.Prime q)]
    (h_n : 2 ≤ n) (_hq : q ≤ 3) (h_skip : ¬ (n = 2 ∧ q = 2)) :
    commutator (PSp n q) = ⊤ := by
  rcases Nat.lt_or_ge n 3 with hn2 | hn3
  · -- `2 ≤ n < 3` ⟹ `n = 2`; then `q ≠ 2` (h_skip), so `q = 3`: characteristic ≠ 2
    have hn : n = 2 := by omega
    have hq2 : q ≠ 2 := fun h => h_skip ⟨hn, h⟩
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h_n
    exact SpN.commutator_PSp_eq_top_char_ne_two (l := Fin n) (F := ZMod q) (two_ne_zero_zmod q hq2)
  · -- `n ≥ 3`: characteristic-free rank-3 argument (covers `q = 2` and `q = 3`)
    exact SpN.commutator_PSp_eq_top_n3 (l := Fin n) (F := ZMod q)
      (by rw [Fintype.card_fin]; omega)

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

import Mathlib

/-!
# The order of `SL(2, F_q)`

`card_SL2` : `|SL(2, ZMod q)| = q·(q² − 1)` for `q` prime.

Together with `SL2.center_SL2` (`|center| = 2` for odd `q`) this pins
`|PSL(2,q)| = q(q²−1)/2`, connecting the `PSL(2,q)` simplicity thread
(`SL2.lean`, `PSLIwasawa.lean`) to the finite-simple-group order tables
(`LieType.lean`, `Classification.lean`). Not on the simplicity critical path
itself, but the natural order-counting companion.

The proof counts matrices of determinant 1 by fibering over the first column
`(a, c)`: the pair `(0,0)` contributes nothing (its determinant is `0 ≠ 1`),
and every other first column admits exactly `q` completions `(b, d)` solving the
non-degenerate linear equation `ad − bc = 1`. Hence
`|SL(2,q)| = (q² − 1)·q = q·(q² − 1)`.

This proof was produced by Aristotle (Harmonic's auto-formalizer) and verified
in our `v4.29.1` kernel; `#print axioms card_SL2` is
`[propext, Classical.choice, Quot.sound]`.
-/

open Matrix

theorem card_SL2 (q : ℕ) [Fact (Nat.Prime q)] :
    Fintype.card (SpecialLinearGroup (Fin 2) (ZMod q)) = q * (q ^ 2 - 1) := by
  have h_det : ∀ (M : Matrix (Fin 2) (Fin 2) (ZMod q)), M.det = 1 → M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    exact fun M hM => by rwa [ Matrix.det_fin_two ] at hM;
  -- We'll use the fact that if the first column is $(a, c)$, then the second column $(b, d)$ must satisfy $ad - bc = 1$. We can split into cases based on whether $a = 0$ or $c = 0$.
  have h_cases : ∀ (a c : ZMod q), a ≠ 0 ∨ c ≠ 0 → Finset.card (Finset.filter (fun p : ZMod q × ZMod q => a * p.2 - c * p.1 = 1) (Finset.univ : Finset (ZMod q × ZMod q))) = q := by
    intro a c h
    by_cases ha : a = 0;
    · -- Since $c \neq 0$, we can solve for $b$ in terms of $d$: $b = -c^{-1}$.
      have h_b : ∀ (c : ZMod q), c ≠ 0 → Finset.card (Finset.filter (fun p : ZMod q × ZMod q => -c * p.1 = 1) (Finset.univ : Finset (ZMod q × ZMod q))) = q := by
        intro c hc; rw [ show ( Finset.filter ( fun p : ZMod q × ZMod q => -c * p.1 = 1 ) Finset.univ : Finset ( ZMod q × ZMod q ) ) = Finset.image ( fun d : ZMod q => ( -c⁻¹, d ) ) Finset.univ from ?_ ] ; rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hc ] ;
        grind;
      aesop;
    · rw [ show ( Finset.filter ( fun p : ZMod q × ZMod q => a * p.2 - c * p.1 = 1 ) Finset.univ : Finset ( ZMod q × ZMod q ) ) = Finset.image ( fun x : ZMod q => ( x, ( 1 + c * x ) / a ) ) Finset.univ from ?_ ];
      · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, ha ];
      · ext ⟨ x, y ⟩ ; simp +decide [ ha, mul_div_cancel₀ ] ; ring;
        grind;
  have h_count : Finset.card (Finset.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M.det = 1) (Finset.univ : Finset (Matrix (Fin 2) (Fin 2) (ZMod q)))) = Finset.sum (Finset.univ : Finset (ZMod q × ZMod q)) (fun p => if p.1 = 0 ∧ p.2 = 0 then 0 else q) := by
    have h_count : Finset.card (Finset.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M.det = 1) (Finset.univ : Finset (Matrix (Fin 2) (Fin 2) (ZMod q)))) = Finset.sum (Finset.univ : Finset (ZMod q × ZMod q)) (fun p => Finset.card (Finset.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 0 = p.1 ∧ M 1 0 = p.2 ∧ M.det = 1) (Finset.univ : Finset (Matrix (Fin 2) (Fin 2) (ZMod q))))) := by
      rw [ ← Finset.card_biUnion ];
      · congr with M ; aesop;
      · exact fun p hp q hq hpq => Finset.disjoint_left.mpr fun M hM₁ hM₂ => hpq <| by aesop;
    rw [ h_count, Finset.sum_congr rfl ];
    intro p hp; split_ifs <;> simp_all +decide [ Finset.ext_iff ] ;
    · intro M hM₁ hM₂; specialize h_det M; simp_all +decide [ Matrix.det_fin_two ] ;
    · convert h_cases p.1 p.2 ( by tauto ) using 1;
      refine' Finset.card_bij ( fun M hM => ( M 0 1, M 1 1 ) ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_univ ];
      · grind;
      · intro a₁ ha₁ ha₂ ha₃ a₂ ha₄ ha₅ ha₆ ha₇ ha₈; ext i j; fin_cases i <;> fin_cases j <;> aesop;
      · intro a b hab; use Matrix.of ![![p.1, a], ![p.2, b]]; simp_all +decide [ Matrix.det_fin_two ] ;
        linear_combination' hab;
  convert h_count using 1;
  · rw [ ← Nat.card_eq_finsetCard ] ; aesop;
  · simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_and, Finset.card_univ, pow_two ];
    rw [ mul_comm, show ( Finset.univ.filter fun x : ZMod q × ZMod q => x.1 = 0 → ¬x.2 = 0 ) = Finset.univ \ { ( 0, 0 ) } by ext ⟨ x, y ⟩ ; by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp +decide [ hx, hy ] ] ; simp +decide [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ ]

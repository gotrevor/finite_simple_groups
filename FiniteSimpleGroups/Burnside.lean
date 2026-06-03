import Mathlib
import FiniteSimpleGroups.Basic
import FiniteSimpleGroups.CharacterTheory

/-!
# Burnside's `p^a q^b` theorem — character-theoretic core reduced to a sharp axiom

`burnside_simple` — *a finite **simple** group all of whose prime divisors lie in `{p, q}`
is solvable* — is the genuinely hard half of Burnside's theorem (Burnside 1904).  This file
machine-checks the **group-theoretic** half of the argument (the classical Sylow / centre
reduction) and isolates the one irreducibly character-theoretic ingredient as a single sharp
axiom, `isSimpleGroup_centralizer_index_not_primePow`.

This mirrors exactly how the repo cracked Bender's cornerstone: reduce a broad statement to one
sharp, clearly-true axiom and machine-check everything around it, so that future laps need only
attack the sharp core.

## The reduction (machine-checked below)

Let `G` be a finite simple group with prime divisors `⊆ {p, q}`.  If `G` is commutative it is
solvable, so assume it is not.  Then `G` is nontrivial and (centre is normal, simplicity) has
**trivial centre** `Z(G) = ⊥`.  Pick any prime `s ∣ |G|` and a Sylow `s`-subgroup `P`; it is
nontrivial, so its centre is nontrivial (`IsPGroup.center_nontrivial`).  Take `g ∈ Z(P)`,
`g ≠ 1`; then `P ≤ C_G(g)`, so the conjugacy-class size `N = [G : C_G(g)] = (C_G(g)).index`
divides `[G : P]`, which is coprime to `s`.  Since `Z(G) = ⊥` and `g ≠ 1`, `g` is not central,
so `N > 1`; and every prime dividing `N` divides `|G|` (so lies in `{p, q}`) yet differs from
`s` — forcing all of them equal, i.e. `N = t ^ k` is a **prime power `> 1`**.  The sharp axiom
says a simple group has no such class, contradiction.

## The sharp axiom

`isSimpleGroup_centralizer_index_not_primePow`: in a finite simple group, the centralizer index
`[G : C_G(g)]` of a nontrivial element is never a prime power `> 1` — equivalently, no nontrivial
element has a conjugacy class of prime-power size `> 1`.  This is Burnside's theorem (Isaacs,
*Character Theory of Finite Groups*, Theorem 3.8 + its corollary; Serre, *Linear Representations*,
§6).  Its proof is the part that needs character theory mathlib `v4.29.1` lacks (algebraic
integrality of character values, the class-sum / central-character argument, column orthogonality);
see `ON-LINE-REQUEST.md` (2026-06-03).
-/

namespace FiniteSimpleGroups

open Subgroup

/-- **Burnside's prime-power class-size lemma (character-theoretic core).**
In a finite simple group `G`, no nontrivial element `g` has a conjugacy class of prime-power
size `> 1`.  The size of the conjugacy class of `g` is the index `(centralizer {g}).index =
[G : C_G(g)]`, so equivalently: that index is never `p ^ k` with `k ≥ 1`.

This is the one irreducibly character-theoretic ingredient of Burnside's `p^a q^b` theorem.
Sketch (Isaacs, *Character Theory*, Thm 3.8): every character value `χ(g)` is an algebraic
integer; the central character maps the class sum to an algebraic integer, so
`[G:C_G(g)]·χ(g)/χ(1)` is an algebraic integer; if `gcd([G:C_G(g)], χ(1)) = 1` then `χ(g)/χ(1)`
is an algebraic integer of absolute value `≤ 1`, hence `χ(g) = 0` or `|χ(g)| = χ(1)`; the
column-orthogonality relation `∑_χ χ(1) χ(g) = 0` (for `g ≠ 1`) together with `-1/p ∉ ℤ̄`
yields a nontrivial `χ` with `p ∤ χ(1)` and `χ(g) ≠ 0`, so `g` acts as a scalar in `χ`; the
elements acting as scalars form a proper nontrivial normal subgroup, contradicting simplicity.

**Now a theorem** (`FiniteSimpleGroups.CharacterTheory.burnside_class_size`), fully machine-checked
with **no custom axioms** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`): the complete
character-theoretic argument — regular-character decomposition via Artin–Wedderburn, central-character
integrality (class sums + Schur), Kronecker, the scalar bridge, and the uniqueness of the trivial
Wedderburn factor (averaging-idempotent nonnegative-trace argument). -/
theorem isSimpleGroup_centralizer_index_not_primePow
    (G : Type*) [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (g : G) (hg : g ≠ 1) (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hidx : (centralizer ({g} : Set G)).index = p ^ k) : False :=
  burnside_class_size hsimple g hg p k hp hk hidx

/-- **Burnside's `p^a q^b` theorem, simple case.**  A finite *simple* group all of whose prime
divisors lie in `{p, q}` is solvable (equivalently: cyclic of prime order — the only finite
simple groups of order `p^a q^b` are the prime-cyclic ones).

Proved here by the classical Sylow / centre reduction to the prime-power class-size lemma
`isSimpleGroup_centralizer_index_not_primePow`. -/
theorem burnside_simple (G : Type*) [Group G] [Finite G] (p q : ℕ)
    (hpq : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q)
    (hsimple : IsSimpleGroup G) : IsSolvable G := by
  classical
  haveI := hsimple
  -- It suffices to prove `G` commutative; assume not.
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  by_contra hncomm
  -- `G` is nontrivial (a subsingleton is commutative).
  haveI hnt : Nontrivial G := by
    rcases subsingleton_or_nontrivial G with hs | hn
    · exact absurd (fun a b => Subsingleton.elim _ _) hncomm
    · exact hn
  haveI : Nonempty G := inferInstance
  -- The centre is normal, hence `⊥` or `⊤`; `⊤` would make `G` commutative, so it is `⊥`.
  have hZ : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso; apply hncomm; intro a b
      have ha : a ∈ center G := h ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  -- Pick a prime `s ∣ |G|`.
  have hcard0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hcard1 : Nat.card G ≠ 1 := by
    intro h
    exact (not_subsingleton G) ((Nat.card_eq_one_iff_unique.mp h).1)
  obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd hcard1
  haveI : Fact s.Prime := ⟨hs⟩
  -- A Sylow `s`-subgroup, which is nontrivial.
  obtain ⟨P⟩ : Nonempty (Sylow s G) := inferInstance
  have hfs : 1 ≤ (Nat.card G).factorization s :=
    (hs.dvd_iff_one_le_factorization hcard0).mp hsdvd
  have hPcard : Nat.card (P : Subgroup G) = s ^ (Nat.card G).factorization s :=
    P.card_eq_multiplicity
  haveI : Nontrivial (P : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPcard]
    calc 1 < s := hs.one_lt
      _ ≤ s ^ (Nat.card G).factorization s := Nat.le_self_pow (by omega) s
  -- The centre of `P` is nontrivial; take a nontrivial central element `z`.
  haveI hZP : Nontrivial (Subgroup.center (P : Subgroup G)) :=
    P.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center (P : Subgroup G))
  set z : (P : Subgroup G) := (c : (P : Subgroup G)) with hzdef
  have hz_mem : z ∈ Subgroup.center (P : Subgroup G) := c.2
  have hzne : z ≠ 1 := fun h => hc1 (Subtype.ext h)
  -- The element `g := ↑z ∈ G` is nontrivial.
  have hgne : (z : G) ≠ 1 := fun h => hzne (OneMemClass.coe_eq_one.mp h)
  -- `P ≤ C_G(g)`, since `z` is central in `P`.
  have hPle : (P : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    intro y hy
    rw [mem_centralizer_iff]
    rintro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hc := (Subgroup.mem_center_iff.mp hz_mem) ⟨y, hy⟩
    have h3 := congrArg (fun w : (P : Subgroup G) => (w : G)) hc
    simp only [Subgroup.coe_mul] at h3
    exact h3.symm
  -- Set `N = [G : C_G(g)]`.  `N ∣ [G : P]`, hence `s ∤ N`.
  have hidx_dvd : (centralizer ({(z : G)} : Set G)).index ∣ (P : Subgroup G).index :=
    index_dvd_of_le hPle
  have hs_notP : ¬ s ∣ (P : Subgroup G).index := P.not_dvd_index
  have hs_notN : ¬ s ∣ (centralizer ({(z : G)} : Set G)).index :=
    fun h => hs_notP (h.trans hidx_dvd)
  -- `N ≠ 1`: else `C_G(g) = ⊤`, so `g ∈ Z(G) = ⊥`, so `g = 1`.
  have hN_ne1 : (centralizer ({(z : G)} : Set G)).index ≠ 1 := by
    intro htop
    rw [Subgroup.index_eq_one, centralizer_eq_top_iff_subset] at htop
    have hmem : (z : G) ∈ center G := htop (Set.mem_singleton _)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hgne hmem
  have hN_ne0 : (centralizer ({(z : G)} : Set G)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hN_dvd_card : (centralizer ({(z : G)} : Set G)).index ∣ Nat.card G :=
    Subgroup.index_dvd_card _
  -- Every prime dividing `N` lies in `{p, q}` and differs from `s`; any two such are equal.
  have key : ∀ d e : ℕ, d.Prime → d ∣ Nat.card G → d ≠ s →
      e.Prime → e ∣ Nat.card G → e ≠ s → d = e := by
    intro d e hd hdc hds he hec hes
    rcases hpq d hd hdc with rfl | rfl <;> rcases hpq e he hec with rfl | rfl <;>
      rcases hpq s hs hsdvd with hsp | hsp <;> simp_all
  -- Hence `N = t ^ k` with `t = N.minFac` prime and `k ≥ 1`.
  have ht : ((centralizer ({(z : G)} : Set G)).index).minFac.Prime := Nat.minFac_prime hN_ne1
  have ht_dvd : ((centralizer ({(z : G)} : Set G)).index).minFac ∣ Nat.card G :=
    (Nat.minFac_dvd _).trans hN_dvd_card
  have ht_ne_s : ((centralizer ({(z : G)} : Set G)).index).minFac ≠ s := by
    intro h
    have hdvd := Nat.minFac_dvd (centralizer ({(z : G)} : Set G)).index
    rw [h] at hdvd
    exact hs_notN hdvd
  have hNeq : (centralizer ({(z : G)} : Set G)).index =
      ((centralizer ({(z : G)} : Set G)).index).minFac ^
        ((centralizer ({(z : G)} : Set G)).index.primeFactorsList.length) := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hN_ne0 ?_
    intro d hd hdvd
    have hd_card : d ∣ Nat.card G := hdvd.trans hN_dvd_card
    have hd_ne_s : d ≠ s := by
      intro h
      rw [h] at hdvd
      exact hs_notN hdvd
    exact key d _ hd hd_card hd_ne_s ht ht_dvd ht_ne_s
  have hk1 : 1 ≤ (centralizer ({(z : G)} : Set G)).index.primeFactorsList.length := by
    rcases Nat.eq_zero_or_pos (centralizer ({(z : G)} : Set G)).index.primeFactorsList.length
      with hk0 | hk0
    · exfalso; rw [hk0, pow_zero] at hNeq; exact hN_ne1 hNeq
    · exact hk0
  exact isSimpleGroup_centralizer_index_not_primePow G hsimple (z : G) hgne _ _ ht hk1 hNeq

end FiniteSimpleGroups

import Mathlib
import FiniteSimpleGroups.Basic
import FiniteSimpleGroups.Classification

/-!
# The CFSG proof strategy — as a *deductive skeleton*

This file states the **architectural milestones** of the CFSG proof and then
*assembles them into a proof of the classification* (`classification_via_program`).

The leaf milestones are `axiom`s (each a decades-long effort by many authors —
not realistically formalizable for years). But the **assembly is a real Lean
proof**: given the milestone axioms, `IsClassified G` follows by case analysis.
This turns the file from documentation into a checkable skeleton — the shape of
the argument is machine-verified even though the leaves are postulated.

```
                    Feit–Thompson (1962)
            "odd order ⇒ solvable", so a nonabelian
             finite simple group has an involution"
                            │
              prime-cyclic  │  has involution
              ┌─────────────┴─────────────┐
              ▼                            ▼
        IsClassified                Aschbacher's dichotomy
        (.cyclic)                   odd type  /  even type
                                   ╱                  ╲
                                  ▼                    ▼
                            odd-type             even-type dichotomy
                            classification    component / characteristic-2
                            (GLS program)      ╱                ╲
                                  │           ▼                  ▼
                                  ▼     component-type      characteristic-2
                            IsClassified  classification    ╱          ╲
                                                      quasithin    non-quasithin
                                                  (Aschbacher–Smith)      │
                                                          ▼               ▼
                                                     IsClassified   IsClassified
```

Each milestone is a separate decades-long effort. The historical narrative is
in `docs/architecture.md`; this file is the logical spine.
-/

namespace FiniteSimpleGroups

/-! ### Milestone 0: Burnside's `p^a q^b` theorem (1904)

Predates CFSG by half a century; not on the deductive spine below, but the
historical seed of the local/character-theoretic method. **Not in mathlib** as
of v4.29.1 (mathlib has Burnside's *transfer* theorem and Burnside's orbit
*lemma*, but not `p^a q^b` solvability — that needs character theory mathlib
doesn't yet carry). So this stays a genuine axiom, not a quick discharge. -/

/-- **Burnside's theorem (1904).** A finite group whose order has at most two
distinct prime divisors is solvable. -/
axiom Burnside_paqb (G : Type*) [Group G] [Finite G]
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (a b : ℕ)
    (h_card : Nat.card G = p ^ a * q ^ b) : IsSolvable G

/-! ### Milestone 1: The Feit–Thompson Odd Order Theorem (1962) -/

/-- **Feit–Thompson Odd Order Theorem.** Every finite group of odd order is
solvable. (255 pages, 1963; Coq-formalized by Gonthier et al. 2013, ~150k
lines; not yet ported to Lean.) -/
axiom Feit_Thompson_odd_order (G : Type*) [Group G] [Finite G]
    (h_odd : Odd (Nat.card G)) : IsSolvable G

/-- **The Feit–Thompson dichotomy (CFSG entry point).** A finite simple group
is either cyclic of prime order, or contains an involution.

**Discharged from `Feit_Thompson_odd_order` + mathlib (2026-05-31).** This was an
axiom; it is now a real theorem. The deep input (Feit–Thompson odd-order) stays
an axiom, but the *dichotomy itself* is elementary on top of it:
* **odd order** ⇒ `Feit_Thompson_odd_order` gives solvable ⇒ a simple solvable
  group is commutative (`IsSimpleGroup.comm_iff_isSolvable`) ⇒ cyclic of prime
  order (`IsSimpleGroup.isCyclic`, `IsSimpleGroup.prime_card`) ⇒ the iso to
  `Multiplicative (ZMod p)` via `mulEquivOfPrimeCardEq`;
* **even order** ⇒ Cauchy (`exists_prime_orderOf_dvd_card`) yields an element of
  order 2, i.e. an involution. -/
theorem feitThompson_dichotomy (G : Type*) [Group G] [IsFSG G] :
    (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p)))
      ∨ (∃ x : G, x ≠ 1 ∧ x ^ 2 = 1) := by
  classical
  haveI : Finite G := IsFSG.finite
  haveI : Fintype G := Fintype.ofFinite G
  by_cases hodd : Odd (Nat.card G)
  · -- odd ⇒ Feit–Thompson ⇒ solvable ⇒ commutative ⇒ cyclic of prime order
    left
    have hsol : IsSolvable G := Feit_Thompson_odd_order G hodd
    have hcomm : ∀ a b : G, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr hsol
    haveI : IsMulCommutative G := ⟨⟨hcomm⟩⟩
    have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
    refine ⟨Nat.card G, hp, ?_⟩
    haveI : Fact (Nat.card G).Prime := ⟨hp⟩
    have hG' : Nat.card (Multiplicative (ZMod (Nat.card G))) = Nat.card G := by
      simp
    exact ⟨mulEquivOfPrimeCardEq (rfl) hG'⟩
  · -- even ⇒ Cauchy gives an element of order 2
    right
    have heven : 2 ∣ Nat.card G := by
      rcases Nat.even_or_odd (Nat.card G) with he | ho
      · exact he.two_dvd
      · exact absurd ho hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2
      (by rwa [Nat.card_eq_fintype_card] at heven)
    refine ⟨x, ?_, ?_⟩
    · intro h; rw [h] at hx; simp [orderOf_one] at hx
    · have := orderOf_dvd_iff_pow_eq_one (n := 2) (x := x)
      rw [hx] at this
      exact this.mp dvd_rfl

/-! ### Milestone 2: Aschbacher's dichotomy (odd type vs even type) -/

/-- A finite simple group is **of odd type** if the involution-centralizer
analysis looks like a Lie group over a field of *odd* characteristic
(involutions are semisimple, sitting in a torus). Highly technical; `opaque`. -/
opaque IsOddType (G : Type*) [Group G] : Prop

/-- A finite simple group is **of even type** (≈ characteristic-2 type) — the
hard branch, where the quasithin sub-case lives. `opaque`. -/
opaque IsEvenType (G : Type*) [Group G] : Prop

/-- **Aschbacher's dichotomy (~1980).** A finite simple group with an
involution is of odd type or of even type (the cases overlap for small groups,
but together they cover everything). -/
axiom aschbacher_dichotomy (G : Type*) [Group G] [IsFSG G]
    (h_invol : ∃ x : G, x ≠ 1 ∧ x ^ 2 = 1) :
    IsOddType G ∨ IsEvenType G

/-! ### Milestone 3: the odd-type case (Gorenstein–Lyons–Solomon program) -/

/-- **Classification of odd-type simple groups (GLS program).** An odd-type
finite simple group is classified. This is the **second-generation** proof —
12 planned AMS volumes, 10 published by 2023. Internally: B-Theorem ⇒
Component Theorem ⇒ standard-form problems, powered by the Signalizer Functor
method and the generalized Fitting subgroup `F*(G)`. -/
axiom oddType_isClassified (G : Type*) [Group G] [IsFSG G]
    (h_odd : IsOddType G) : IsClassified G

/-! ### Milestone 4: the even-type case -/

/-- A simple group of even type is of **component type** (a Lie-type component
over `F_{2^k}` in the centralizer of an involution). `opaque`. -/
opaque IsComponentType (G : Type*) [Group G] : Prop

/-- A simple group of even type is of **characteristic-2 type** (the whole
analysis happens inside `O_2` of the involution centralizer). `opaque`. -/
opaque IsCharacteristic2Type (G : Type*) [Group G] : Prop

/-- Even-type groups split into component type and characteristic-2 type. -/
axiom evenType_dichotomy (G : Type*) [Group G] [IsFSG G]
    (h_even : IsEvenType G) :
    IsComponentType G ∨ IsCharacteristic2Type G

/-- **Component-type classification.** A component-type simple group is
classified (Aschbacher's Component Theorem [A4], Cole Prize work; Gilman–Griess
for the standard-component endgame, Gorenstein's Step XVI). -/
axiom componentType_isClassified (G : Type*) [Group G] [IsFSG G]
    (h_comp : IsComponentType G) : IsClassified G

/-! ### Milestone 5: the characteristic-2 case (incl. quasithin) -/

/-- A characteristic-2-type simple group is **quasithin** if its `e(G)`
(maximum 2-local 2-rank) is `≤ 2`. The case that almost unraveled CFSG:
Mason's 1980s manuscript was found incomplete; Aschbacher–Smith redid it from
scratch (~1200 pages, AMS 2004) — the last brick, fixing CFSG's completion
date at 2004. `opaque`. -/
opaque IsQuasithin (G : Type*) [Group G] : Prop

/-- **Quasithin classification (Aschbacher–Smith, 2004).** -/
axiom quasithin_isClassified (G : Type*) [Group G] [IsFSG G]
    (h : IsCharacteristic2Type G) (hq : IsQuasithin G) : IsClassified G

/-- **Non-quasithin characteristic-2 classification** (`e(G) ≥ 3`): the
Gorenstein–Lyons Trichotomy Theorem (structural capstone, Steps XI/XV) feeding
the uniqueness case (Aschbacher, Step X) and the `GF(2)`-type case
(Timmesfeld/Smith). -/
axiom nonQuasithin_char2_isClassified (G : Type*) [Group G] [IsFSG G]
    (h : IsCharacteristic2Type G) (hq : ¬ IsQuasithin G) : IsClassified G

/-! ### The assembly: CFSG from the milestones

This is a **real proof** (case analysis), not an axiom. It checks that the
milestone *interfaces* compose into `IsClassified G`. The raw `axiom CFSG` in
`Classification.lean` is the headline statement; this is the same conclusion
derived from the named program steps. -/

/-- **The Classification, assembled from the program milestones.** Every
finite simple group is classified — proved here by threading Feit–Thompson,
Aschbacher's dichotomy, and the odd/even/component/char-2/quasithin
classifications together. The leaves are axioms; the *logic* is verified. -/
theorem classification_via_program (G : Type*) [Group G] [IsFSG G] :
    IsClassified G := by
  rcases feitThompson_dichotomy G with hcyc | hinv
  · -- Feit–Thompson: prime-cyclic case
    exact .cyclic hcyc
  · -- has an involution: enter the dichotomy machine
    rcases aschbacher_dichotomy G hinv with hodd | heven
    · exact oddType_isClassified G hodd
    · rcases evenType_dichotomy G heven with hcomp | hchar2
      · exact componentType_isClassified G hcomp
      · by_cases hqt : IsQuasithin G
        · exact quasithin_isClassified G hchar2 hqt
        · exact nonQuasithin_char2_isClassified G hchar2 hqt

end FiniteSimpleGroups

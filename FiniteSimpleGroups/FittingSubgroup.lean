import Mathlib

/-!
# The Fitting subgroup `F(G)` — a foundational brick mathlib lacks

Solomon's history (Bulletin AMS 38, 2001, p. 343) frames the whole CFSG
architecture through the **generalized Fitting subgroup** `F*(G) = E(G)·F(G)`:

* B-Theorem ⟹ `F(G) = 1`, so `F*(G) = E(G)` (a product of simple groups);
* Component Theorem ⟹ `F*(G)` is a *single* simple group;
* CFSG ⟹ classify all `G` with `F*(G)` nonabelian simple.

So `F(G)` (and then `F*(G)`) is the object the entire proof hangs on. mathlib
(v4.29.1) has **no group-theoretic Fitting subgroup** — every `Fitting` in the
library is the Lie-algebra / module Fitting *decomposition*, a different notion.
This file defines the ordinary Fitting subgroup and proves what's reachable.

## What's real vs. cited here

* `fittingSubgroup` — the definition (join of normal nilpotent subgroups).
* `normal_nilpotent_le_fittingSubgroup`, `center_le_fittingSubgroup` — **proved**.
* Step-1 Sylow bricks (`sylow_characteristic_of_isNilpotent`,
  `sylow_normal_of_normal_nilpotent`) — **proved**.
* `sSup_normal_of_forall_normal`, `pCore`, `pCore_normal` — **proved**.
* `normal_pgroup_le_fittingSubgroup` — **proved**.
* `isPGroup_pCore` (that `O_p(G)` is a `p`-group) — **proved** via
  `Finset.sup_induction` over the (finite) set of normal `p`-subgroups.
* `pCore_le_fittingSubgroup` (`O_p(G) ≤ F(G)`) — **proved**.
* `fittingSubgroup_normal`, `fittingSubgroup_isNilpotent` (**Fitting's Theorem**)
  — still cited `axiom`s (step 4). (Ref: Isaacs, *Finite Group Theory*, Thm 9.8.)
-/

namespace FiniteSimpleGroups

open scoped IsMulCommutative

/-- The **Fitting subgroup** `F(G)`: the supremum (join) of all normal
nilpotent subgroups of `G`. -/
def fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {H : Subgroup G | H.Normal ∧ Group.IsNilpotent H}

/-- **Universal property.** Every normal nilpotent subgroup lies in `F(G)`. -/
theorem normal_nilpotent_le_fittingSubgroup {G : Type*} [Group G]
    (H : Subgroup G) (hN : H.Normal) (hnil : Group.IsNilpotent H) :
    H ≤ fittingSubgroup G :=
  le_sSup ⟨hN, hnil⟩

/-- The **center is contained in the Fitting subgroup**: normal + abelian ⇒
nilpotent ⇒ inside `F(G)`. -/
theorem center_le_fittingSubgroup {G : Type*} [Group G] :
    Subgroup.center G ≤ fittingSubgroup G :=
  normal_nilpotent_le_fittingSubgroup (Subgroup.center G) inferInstance
    CommGroup.isNilpotent

/-! ### Step 1: Sylows of normal nilpotent subgroups -/

/-- In a finite **nilpotent** group every Sylow subgroup is characteristic.
Chain: nilpotent ⇒ normalizer condition ⇒ Sylow normal ⇒ Sylow characteristic. -/
theorem sylow_characteristic_of_isNilpotent {N : Type*} [Group N] [Finite N]
    [Group.IsNilpotent N] {p : ℕ} [Fact p.Prime] (P : Sylow p N) :
    (↑P : Subgroup N).Characteristic :=
  P.characteristic_of_normal
    (P.normal_of_normalizerCondition normalizerCondition_of_isNilpotent)

/-- **Sylow subgroups of a normal nilpotent subgroup are normal in the whole
group.** Characteristic in `N` + `N ⊴ G` ⇒ normal in `G`. -/
theorem sylow_normal_of_normal_nilpotent {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent N)
    {p : ℕ} [Fact p.Prime] (P : Sylow p N) :
    ((↑P : Subgroup N).map N.subtype).Normal := by
  haveI := hN
  haveI := hnil
  haveI := sylow_characteristic_of_isNilpotent P
  infer_instance

/-! ### Step 2: the hand-rolled `p`-core `O_p(G)` (partial)

`sSup` of normal subgroups is normal (mathlib has only the `iInf` version).
`pCore G p` is the join of all normal `p`-subgroups. Its normality is proved;
that it is itself a `p`-group (`isPGroup_pCore`) is **not yet done**. -/

/-- **The `sSup` of a set of normal subgroups is normal.** Conjugation is a
pointwise smul = `map` of a monoid hom (`pointwise_smul_def`); `map` preserves
`sSup` (`gc_map_comap.l_sSup`); each normal member is conj-fixed; close via
`Normal.of_conjugate_fixed`. -/
theorem sSup_normal_of_forall_normal {G : Type*} [Group G] {S : Set (Subgroup G)}
    (hS : ∀ K ∈ S, K.Normal) : (sSup S).Normal := by
  refine Subgroup.Normal.of_conjugate_fixed (fun g => ?_)
  rw [Subgroup.pointwise_smul_def, (Subgroup.gc_map_comap _).l_sSup, sSup_eq_iSup]
  refine iSup_congr (fun K => iSup_congr (fun hK => ?_))
  rw [← Subgroup.pointwise_smul_def]
  haveI := hS K hK
  exact Subgroup.Normal.conj_smul_eq_self g K

/-- The **`p`-core `O_p(G)`** (hand-rolled): the join of all normal
`p`-subgroups of `G`. mathlib has no such definition. -/
def pCore (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q}

/-- `O_p(G)` is normal — a join of normal subgroups. -/
theorem pCore_normal {G : Type*} [Group G] {p : ℕ} : (pCore G p).Normal :=
  sSup_normal_of_forall_normal (fun _ hK => hK.1)

/-- **`O_p(G)` is a `p`-group.** `pCore` is the join of all normal `p`-subgroups;
since `G` is finite that indexing set is a finite `Finset`, so `Finset.sup_induction`
(based at `⊥` via `IsPGroup.of_bot`, stepped by `IsPGroup.to_sup_of_normal_right`)
carries the joint motive "is a `p`-group and is normal" up the join. Routing the
induction through an explicit `T : Finset (Subgroup G)` is what lets `OrderBot
(Subgroup G)` resolve (the bare `Finset.sup` form left it a stuck metavariable). -/
theorem isPGroup_pCore {G : Type*} [Group G] [Finite G] {p : ℕ} :
    IsPGroup p (pCore G p) := by
  classical
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  have hSfin : {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q}.Finite := Set.toFinite _
  have hkey : ∀ T : Finset (Subgroup G), (∀ K ∈ T, K.Normal ∧ IsPGroup p K) →
      IsPGroup p (T.sup id : Subgroup G) ∧ (T.sup id : Subgroup G).Normal := by
    intro T hT
    refine Finset.sup_induction (p := fun J : Subgroup G => IsPGroup p J ∧ J.Normal)
      ⟨IsPGroup.of_bot, inferInstance⟩ ?_ (fun K hK => ⟨(hT K hK).2, (hT K hK).1⟩)
    rintro a ⟨hap, han⟩ b ⟨hbp, hbn⟩
    haveI := han; haveI := hbn
    exact ⟨IsPGroup.to_sup_of_normal_right hap hbp, inferInstance⟩
  have hpc : pCore G p = hSfin.toFinset.sup id := by
    unfold pCore
    rw [Finset.sup_id_eq_sSup, hSfin.coe_toFinset]
  rw [hpc]
  exact (hkey hSfin.toFinset (fun K hK => hSfin.mem_toFinset.mp hK)).1

/-! ### Step 3: normal `p`-subgroups live in `F(G)` -/

/-- A **normal `p`-subgroup lies inside `F(G)`.** A finite `p`-group is nilpotent
(`IsPGroup.isNilpotent`), so it is normal nilpotent and the universal property
places it in `F(G)`. -/
theorem normal_pgroup_le_fittingSubgroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup G} (hQ : Q.Normal) (hp : IsPGroup p Q) :
    Q ≤ fittingSubgroup G :=
  normal_nilpotent_le_fittingSubgroup Q hQ hp.isNilpotent

/-- **`O_p(G) ≤ F(G)`.** The `p`-core is a normal `p`-subgroup, so it lands in
the Fitting subgroup by `normal_pgroup_le_fittingSubgroup`. -/
theorem pCore_le_fittingSubgroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] : pCore G p ≤ fittingSubgroup G :=
  normal_pgroup_le_fittingSubgroup pCore_normal isPGroup_pCore

/-! ### Step 4, sub-goal 1: `F(G) ≤ ⨆_p O_p(G)` -/

/-- **The Sylow subgroups generate any finite group.** The join, over all primes
`p` and all Sylow `p`-subgroups `P`, of the `P` is `⊤`. Proof by cardinality: the
join `S` contains, for each prime `p`, a Sylow `p`-subgroup of order
`p ^ (card K).factorization p`, so that prime power divides `Nat.card S`
(Lagrange); hence `Nat.card K ∣ Nat.card S` (`factorization_le_iff_dvd`), forcing
`S = ⊤`. -/
theorem iSup_prime_sylow_eq_top (K : Type*) [Group K] [Finite K] :
    ⨆ (p : ℕ) (_ : p.Prime) (P : Sylow p K), (↑P : Subgroup K) = ⊤ := by
  classical
  set S : Subgroup K := ⨆ (p : ℕ) (_ : p.Prime) (P : Sylow p K), (↑P : Subgroup K) with hS
  have hSne : Nat.card S ≠ 0 := Nat.card_pos.ne'
  apply Subgroup.eq_top_of_card_eq
  refine Nat.dvd_antisymm ?_ ?_
  · rw [← Subgroup.card_top (G := K)]
    exact Subgroup.card_dvd_of_le le_top
  · rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' hSne, Finsupp.le_iff]
    intro p hp_mem
    rw [Nat.support_factorization] at hp_mem
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨P⟩ : Nonempty (Sylow p K) := Sylow.nonempty
    have hPS : (↑P : Subgroup K) ≤ S := by
      rw [hS]
      exact le_iSup_of_le p
        (le_iSup_of_le hpp (le_iSup (fun Q : Sylow p K => (↑Q : Subgroup K)) P))
    have hdvd : Nat.card (P : Subgroup K) ∣ Nat.card S := Subgroup.card_dvd_of_le hPS
    rw [Sylow.card_eq_multiplicity] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hSne).mp hdvd

/-- **`F(G) ≤ ⨆_p O_p(G)`.** Each normal nilpotent `N ⊴ G` is the join of its
Sylow subgroups (`iSup_prime_sylow_eq_top` on `↥N`); each such Sylow, pushed into
`G`, is a *normal* `p`-subgroup (`sylow_normal_of_normal_nilpotent`) hence lands in
`O_p(G)`. Summing over `N` gives the bound. -/
theorem fittingSubgroup_le_iSup_pCore (G : Type*) [Group G] [Finite G] :
    fittingSubgroup G ≤ ⨆ p, pCore G p := by
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  have key : N = ⨆ (p : ℕ) (_ : p.Prime) (P : Sylow p ↥N),
      ((↑P : Subgroup ↥N).map N.subtype) := by
    simp only [← Subgroup.map_iSup]
    rw [iSup_prime_sylow_eq_top ↥N, ← MonoidHom.range_eq_map, N.range_subtype]
  rw [key]
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hnorm := sylow_normal_of_normal_nilpotent hN hnil P
  have hpg : IsPGroup p ((↑P : Subgroup ↥N).map N.subtype) :=
    P.isPGroup'.of_equiv ((↑P : Subgroup ↥N).equivMapOfInjective N.subtype N.subtype_injective)
  exact (le_sSup (show ((↑P : Subgroup ↥N).map N.subtype) ∈
    {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} from ⟨hnorm, hpg⟩)).trans (le_iSup (pCore G) p)

/-- **Fitting's Theorem (normality half).** `F(G)` is a normal subgroup.
Cited; see step 4 in `docs/fitting-roadmap.md`. -/
axiom fittingSubgroup_normal (G : Type*) [Group G] : (fittingSubgroup G).Normal

/-- **Fitting's Theorem (nilpotency half).** For a finite group, `F(G)` is
nilpotent. Cited (Isaacs Thm 9.8); discharge route in `docs/fitting-roadmap.md`. -/
axiom fittingSubgroup_isNilpotent (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent (fittingSubgroup G)

end FiniteSimpleGroups

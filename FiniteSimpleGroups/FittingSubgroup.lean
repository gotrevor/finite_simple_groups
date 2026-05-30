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

/-- **`F(G) ≤ ⨆_p O_p(G)`** (join over *primes* `p`). Each normal nilpotent
`N ⊴ G` is the join of its Sylow subgroups (`iSup_prime_sylow_eq_top` on `↥N`);
each such Sylow, pushed into `G`, is a *normal* `p`-subgroup
(`sylow_normal_of_normal_nilpotent`) hence lands in `O_p(G)`. Summing over `N`
gives the bound. (The join must range over primes: for *composite* `p`,
`IsPGroup p` describes a `π`-group and `O_p(G)` need not be nilpotent.) -/
theorem fittingSubgroup_le_iSup_pCore (G : Type*) [Group G] [Finite G] :
    fittingSubgroup G ≤ ⨆ (p : ℕ) (_ : p.Prime), pCore G p := by
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
    {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} from ⟨hnorm, hpg⟩)).trans
    (le_iSup_of_le p (le_iSup (fun _ : p.Prime => pCore G p) hp))

/-- **`⨆_p O_p(G) ≤ F(G)`** (join over primes). Each `O_p(G)` is a normal
`p`-subgroup, so it lies in `F(G)` by `pCore_le_fittingSubgroup`. -/
theorem iSup_pCore_le_fittingSubgroup (G : Type*) [Group G] [Finite G] :
    ⨆ (p : ℕ) (_ : p.Prime), pCore G p ≤ fittingSubgroup G :=
  iSup_le fun p => iSup_le fun hp => by
    haveI : Fact p.Prime := ⟨hp⟩; exact pCore_le_fittingSubgroup

/-- **`F(G) = ⨆_p O_p(G)`** (join over primes). The Fitting subgroup is exactly the
join of the `p`-cores. -/
theorem fittingSubgroup_eq_iSup_pCore (G : Type*) [Group G] [Finite G] :
    fittingSubgroup G = ⨆ (p : ℕ) (_ : p.Prime), pCore G p :=
  le_antisymm (fittingSubgroup_le_iSup_pCore G) (iSup_pCore_le_fittingSubgroup G)

/-! ### Step 4, sub-goal 2: `⨆_p O_p(G)` is nilpotent -/

/-- **`O_p(G) = 1` when `p ∤ |G|`.** The `p`-core is a `p`-group, so its order is a
power of `p` dividing `|G|`; if `p ∤ |G|` that power is `p⁰ = 1`. -/
theorem pCore_eq_bot_of_not_dvd (G : Type*) [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ Nat.card G) : pCore G p = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_pCore (G := G) (p := p))
  have hdvd : Nat.card (pCore G p) ∣ Nat.card G := by
    have h := Subgroup.card_dvd_of_le (le_top : pCore G p ≤ ⊤)
    rwa [Subgroup.card_top] at h
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [Subgroup.eq_bot_iff_card, hk, hk0, pow_zero]
  · exact absurd (dvd_trans (dvd_pow_self p hkpos.ne') (hk ▸ hdvd)) hp

/-- **`⨆_p O_p(G)` is nilpotent** (join over primes). The `p`-cores are normal
with pairwise coprime orders, so they pairwise commute and are independent: the
canonical map `∏_{p ∣ |G|} O_p(G) → G` (`Subgroup.noncommPiCoprod`) is injective
with range `⨆_p O_p(G)`, giving `⨆_p O_p(G) ≃* ∏_{p ∣ |G|} O_p(G)`. Each factor is
a nilpotent `p`-group, a finite product of nilpotent groups is nilpotent
(`isNilpotent_pi`), and nilpotency transports across the equiv. -/
theorem iSup_pCore_isNilpotent (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent ↥(⨆ (p : ℕ) (_ : p.Prime), pCore G p) := by
  classical
  haveI : ∀ i : (Nat.card G).primeFactors, Fintype (pCore G (i : ℕ)) :=
    fun _ => Fintype.ofFinite _
  -- p-cores at distinct prime factors commute (normal + disjoint by coprimality)
  have hcomm : Pairwise (fun i j : (Nat.card G).primeFactors =>
      ∀ x y : G, x ∈ pCore G (i : ℕ) → y ∈ pCore G (j : ℕ) → Commute x y) := by
    intro i j hij
    haveI : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    haveI : Fact (j : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors j.2⟩
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    exact fun x y hx hy => Subgroup.commute_of_normal_of_disjoint _ _ pCore_normal pCore_normal
      (IsPGroup.disjoint_of_ne (i : ℕ) (j : ℕ) hne _ _ isPGroup_pCore isPGroup_pCore) x y hx hy
  -- and are independent (pairwise coprime orders)
  have hind : iSupIndep (fun i : (Nat.card G).primeFactors => pCore G (i : ℕ)) := by
    apply Subgroup.independent_of_coprime_order hcomm
    intro i j hij
    haveI : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    haveI : Fact (j : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors j.2⟩
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne (i : ℕ) (j : ℕ) hne _ _ isPGroup_pCore isPGroup_pCore
  -- internal direct product: ∏_p O_p ≃* ⨆_p O_p
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hrange : (Subgroup.noncommPiCoprod hcomm).range
      = ⨆ i : (Nat.card G).primeFactors, pCore G (i : ℕ) := Subgroup.noncommPiCoprod_range
  have e : (∀ i : (Nat.card G).primeFactors, pCore G (i : ℕ))
      ≃* ↥(⨆ i : (Nat.card G).primeFactors, pCore G (i : ℕ)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  -- each factor is a nilpotent p-group ⟹ finite product nilpotent ⟹ join nilpotent
  haveI : ∀ i : (Nat.card G).primeFactors, Group.IsNilpotent (pCore G (i : ℕ)) := fun i => by
    haveI : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    exact isPGroup_pCore.isNilpotent
  have hnil : Group.IsNilpotent ↥(⨆ i : (Nat.card G).primeFactors, pCore G (i : ℕ)) :=
    nilpotent_of_mulEquiv e
  -- bridge the prime-indexed join to the primeFactors-indexed join
  have heq : (⨆ (p : ℕ) (_ : p.Prime), pCore G p)
      = ⨆ i : (Nat.card G).primeFactors, pCore G (i : ℕ) := by
    apply le_antisymm
    · refine iSup_le fun p => iSup_le fun hp => ?_
      haveI : Fact p.Prime := ⟨hp⟩
      by_cases hd : p ∣ Nat.card G
      · exact le_iSup (fun i : (Nat.card G).primeFactors => pCore G (i : ℕ))
          ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.card_pos.ne'⟩⟩
      · rw [pCore_eq_bot_of_not_dvd G hd]; exact bot_le
    · refine iSup_le fun i => le_iSup_of_le (i : ℕ)
        (le_iSup (fun _ : (i : ℕ).Prime => pCore G (i : ℕ))
          (Nat.prime_of_mem_primeFactors i.2))
  rw [heq]; exact hnil

/-- **Fitting's Theorem (nilpotency half).** For a finite group, `F(G)` is
nilpotent. `F(G) = ⨆_p O_p(G)` (`fittingSubgroup_eq_iSup_pCore`) and that join is
nilpotent (`iSup_pCore_isNilpotent`). (Ref: Isaacs, *Finite Group Theory*, 9.8.) -/
theorem fittingSubgroup_isNilpotent (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent (fittingSubgroup G) := by
  rw [fittingSubgroup_eq_iSup_pCore]; exact iSup_pCore_isNilpotent G

/-- **Fitting's Theorem (normality half).** `F(G)` is a normal subgroup: it is the
`sSup` of subgroups every one of which is normal, so `sSup_normal_of_forall_normal`
applies directly. -/
theorem fittingSubgroup_normal (G : Type*) [Group G] : (fittingSubgroup G).Normal :=
  sSup_normal_of_forall_normal (fun _ hK => hK.1)

end FiniteSimpleGroups

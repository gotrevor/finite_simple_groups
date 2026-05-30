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
* `normal_nilpotent_le_fittingSubgroup` — **proved** (universal property).
* `center_le_fittingSubgroup` — **proved** (center is normal + abelian ⇒
  nilpotent ⇒ inside `F(G)`).
* Step-1 Sylow bricks, the `pCore` (hand-rolled `O_p`), and step-3
  `normal_pgroup_le_fittingSubgroup` — **proved**, see below.
* `fittingSubgroup_normal`, `fittingSubgroup_isNilpotent` (**Fitting's Theorem**)
  — still cited `axiom`s. Discharging them is step 4 (see `docs/fitting-roadmap.md`).
  (Ref: Isaacs, *Finite Group Theory*, Thm 9.8; Kurzweil–Stellmacher §6.)
-/

namespace FiniteSimpleGroups

open scoped IsMulCommutative

/-- The **Fitting subgroup** `F(G)`: the supremum (join) of all normal
nilpotent subgroups of `G`.

For a finite group this is itself a normal nilpotent subgroup — the unique
*largest* one (Fitting's Theorem, `fittingSubgroup_isNilpotent` below). -/
def fittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {H : Subgroup G | H.Normal ∧ Group.IsNilpotent H}

/-- **Universal property.** Every normal nilpotent subgroup lies in `F(G)`.
Immediate from the definition as a supremum. -/
theorem normal_nilpotent_le_fittingSubgroup {G : Type*} [Group G]
    (H : Subgroup G) (hN : H.Normal) (hnil : Group.IsNilpotent H) :
    H ≤ fittingSubgroup G :=
  le_sSup ⟨hN, hnil⟩

/-- The **center is contained in the Fitting subgroup**: it is normal and
abelian, hence nilpotent. A complete proof — the first concrete fact about
`F(G)`, and a sanity check that the definition behaves. -/
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
group.** If `N ⊴ G` is nilpotent, its (unique) Sylow `p`-subgroup is
characteristic in `N`, and a characteristic subgroup of a normal subgroup is
normal in `G`. -/
theorem sylow_normal_of_normal_nilpotent {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} (hN : N.Normal) (hnil : Group.IsNilpotent N)
    {p : ℕ} [Fact p.Prime] (P : Sylow p N) :
    ((↑P : Subgroup N).map N.subtype).Normal := by
  haveI := hN
  haveI := hnil
  haveI := sylow_characteristic_of_isNilpotent P
  infer_instance

/-! ### Step 2: the hand-rolled `p`-core `O_p(G)`

`sSup` of a set of normal subgroups is normal (mathlib has the `iInf` version
but not this one). Then `pCore G p`, the join of all normal `p`-subgroups, is
itself a normal `p`-subgroup — the (hand-rolled) `p`-core. -/

/-- **The `sSup` of a set of normal subgroups is normal.** Proof: conjugation
acts as a pointwise smul, which is the `map` of a monoid endomorphism
(`pointwise_smul_def`); `map` is a left adjoint (`gc_map_comap`) so it preserves
`sSup` (`GaloisConnection.l_sSup`); each normal member is fixed by conjugation
(`Normal.conj_smul_eq_self`), so the image join collapses back to `sSup S`.
Closes via `Normal.of_conjugate_fixed`. -/
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

/-- `O_p(G)` is normal — a join of normal subgroups
(`sSup_normal_of_forall_normal`). -/
theorem pCore_normal {G : Type*} [Group G] {p : ℕ} : (pCore G p).Normal :=
  sSup_normal_of_forall_normal (fun _ hK => hK.1)

/-- **`O_p(G)` is a `p`-group.** The defining set of normal `p`-subgroups is
finite (`Finite G`), so `O_p(G)` is a `Finset.sup`; induct with
`IsPGroup.to_sup_of_normal_right`, carrying *normal ∧ p-group* jointly through the
induction (the `to_sup` step needs the right operand normal). -/
theorem isPGroup_pCore {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p (pCore G p) := by
  have hfin : {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q}.Finite := Set.toFinite _
  have key : (pCore G p).Normal ∧ IsPGroup p (pCore G p) := by
    rw [pCore, ← hfin.coe_toFinset, ← Finset.sup_id_eq_sSup]
    refine Finset.sup_induction ?_ ?_ ?_
    · exact ⟨inferInstance, IsPGroup.of_bot⟩
    · rintro a ⟨ha_n, ha_p⟩ b ⟨hb_n, hb_p⟩
      haveI := ha_n; haveI := hb_n
      exact ⟨inferInstance, IsPGroup.to_sup_of_normal_right ha_p hb_p⟩
    · intro Q hQ
      rw [Set.Finite.mem_toFinset] at hQ
      exact hQ
  exact key.2

/-! ### Step 3: normal `p`-subgroups live in `F(G)` -/

/-- A **normal `p`-subgroup lies inside `F(G)`.** A finite `p`-group is nilpotent
(`IsPGroup.isNilpotent`), so a normal `p`-subgroup is normal nilpotent and the
universal property places it in `F(G)`. -/
theorem normal_pgroup_le_fittingSubgroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup G} (hQ : Q.Normal) (hp : IsPGroup p Q) :
    Q ≤ fittingSubgroup G :=
  normal_nilpotent_le_fittingSubgroup Q hQ hp.isNilpotent

/-- `O_p(G) ≤ F(G)` — the `p`-core is a normal `p`-subgroup (`pCore_normal`,
`isPGroup_pCore`), hence inside the Fitting subgroup. -/
theorem pCore_le_fittingSubgroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] : pCore G p ≤ fittingSubgroup G :=
  normal_pgroup_le_fittingSubgroup pCore_normal isPGroup_pCore

/-- **Fitting's Theorem (normality half).** `F(G)` is a normal subgroup.
Cited; see step 4 in `docs/fitting-roadmap.md`. -/
axiom fittingSubgroup_normal (G : Type*) [Group G] : (fittingSubgroup G).Normal

/-- **Fitting's Theorem (nilpotency half).** For a finite group, `F(G)` is
nilpotent — hence the unique largest normal nilpotent subgroup. Cited (Isaacs
Thm 9.8); the discharge route (`F(G) = ⨆_p O_p(G)`, nilpotent via coprime
internal direct product) is step 4 in `docs/fitting-roadmap.md`. -/
axiom fittingSubgroup_isNilpotent (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent (fittingSubgroup G)

end FiniteSimpleGroups

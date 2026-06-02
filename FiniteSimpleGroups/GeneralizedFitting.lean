import FiniteSimpleGroups.LayerNormal
import FiniteSimpleGroups.FittingSubgroup
import FiniteSimpleGroups.MinimalNormal
import FiniteSimpleGroups.SolubleFittingKernel
import FiniteSimpleGroups.LayerQuotient

/-!
# The generalized Fitting subgroup `F*(G)`

The **generalized Fitting subgroup** `F*(G) = E(G)·F(G)` is the object the whole
CFSG architecture hangs on (Solomon, Bull. AMS 38, 2001, p. 343). It joins the two
bricks built in the prior files:

* the **layer** `E(G)` (`Components.lean`/`LayerNormal.lean`) — the join of the
  components, now known to be normal (`layer_normal`);
* the **Fitting subgroup** `F(G)` (`FittingSubgroup.lean`) — the join of the normal
  nilpotent subgroups, normal and nilpotent (`fittingSubgroup_normal`).

Since `E(G)` and `F(G)` are both normal, `F*(G) = E(G) ⊔ F(G)` is normal too — the
first fact below. The deep property that makes `F*(G)` the cornerstone of the theory
is that it is **self-centralizing**, `C_G(F*(G)) ≤ F*(G)`: in a (suitable) group the
structure is controlled by `F*(G)`. That is the next target; this file establishes
the definition and the normality.

## Main definitions

* `genFittingSubgroup G` (`F*(G)`) — `layer G ⊔ fittingSubgroup G`.

## Main results

* `genFittingSubgroup_normal` — `F*(G)` is normal.
* `layer_le_genFittingSubgroup`, `fittingSubgroup_le_genFittingSubgroup` — both
  factors lie in `F*(G)`.
* `genFittingSubgroup_eq_layer_of_fittingSubgroup_eq_bot` /
  `..._eq_fittingSubgroup_of_layer_eq_bot` — the degenerate cases (e.g. the
  B-theorem reduction `F(G) = 1 ⟹ F*(G) = E(G)`).
* `genFittingSubgroup_self_centralizing` (**axiom**, finite `G`) — Bender's
  cornerstone `C_G(F*(G)) ≤ F*(G)`; and its corollary
  `centralizer_genFittingSubgroup_eq_center` (`C_G(F*(G)) = Z(F*(G))`).
-/

namespace FiniteSimpleGroups

universe u

variable {G : Type*} [Group G]

/-- The **generalized Fitting subgroup** `F*(G) = E(G)·F(G)`, realized as the join
`E(G) ⊔ F(G)` of the layer and the Fitting subgroup. -/
def genFittingSubgroup (G : Type*) [Group G] : Subgroup G :=
  layer G ⊔ fittingSubgroup G

/-- The layer `E(G)` lies in `F*(G)`. -/
theorem layer_le_genFittingSubgroup : layer G ≤ genFittingSubgroup G :=
  le_sup_left

/-- The Fitting subgroup `F(G)` lies in `F*(G)`. -/
theorem fittingSubgroup_le_genFittingSubgroup : fittingSubgroup G ≤ genFittingSubgroup G :=
  le_sup_right

/-- **`F*(G)` is normal.** It is the join of the two normal subgroups `E(G)`
(`layer_normal`) and `F(G)` (`fittingSubgroup_normal`). -/
theorem genFittingSubgroup_normal (G : Type*) [Group G] :
    (genFittingSubgroup G).Normal := by
  haveI := layer_normal (G := G)
  haveI := fittingSubgroup_normal G
  exact Subgroup.sup_normal (layer G) (fittingSubgroup G)

/-- **`F*(N) ≤ F*(G)` for a normal subgroup `N ⊴ G`** (finite `G`). Both factors push
forward along the inclusion `N ↪ G`: `E(N) ≤ E(G)` (`layer_map_subtype_le`) and
`F(N) ≤ F(G)` (`fittingSubgroup_map_subtype_le`), and `map` distributes over the join.
This monotonicity is the structural step the induction in Bender's cornerstone
(`genFittingSubgroup_self_centralizing`) runs on: applied to `N = C_G(F*(G))`, it gives
`F*(C_G(F*(G))) ≤ F*(G)`. -/
theorem genFittingSubgroup_map_subtype_le {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] :
    (genFittingSubgroup N).map N.subtype ≤ genFittingSubgroup G := by
  rw [genFittingSubgroup, Subgroup.map_sup]
  exact sup_le_sup layer_map_subtype_le fittingSubgroup_map_subtype_le

/-- If the Fitting subgroup is trivial then `F*(G) = E(G)`. This is the shape of the
**B-theorem reduction**: once `F(G) = 1`, the generalized Fitting subgroup collapses
to the layer, a (central) product of quasisimple components. -/
theorem genFittingSubgroup_eq_layer_of_fittingSubgroup_eq_bot
    (h : fittingSubgroup G = ⊥) : genFittingSubgroup G = layer G := by
  rw [genFittingSubgroup, h, sup_bot_eq]

/-- If the layer is trivial then `F*(G) = F(G)` — the soluble case, where the
generalized Fitting subgroup is just the ordinary Fitting subgroup. -/
theorem genFittingSubgroup_eq_fittingSubgroup_of_layer_eq_bot
    (h : layer G = ⊥) : genFittingSubgroup G = fittingSubgroup G := by
  rw [genFittingSubgroup, h, bot_sup_eq]

-- `layer_quotient_center_eq_bot` (a central quotient of a component-free group is
-- component-free) is proved in `LayerQuotient.lean` and imported above. It was the last
-- residual axiom of Bender's cornerstone; the cornerstone is now axiom-free.

/-- **Order-bounded solvability of the component-free central case**, by strong induction
on `|G|`. A finite group with no components (`layer G = ⊥`) and central Fitting subgroup
(`F(G) ≤ Z(G)`) is solvable.

* `Z(G) = ⊤`: `G` abelian.
* `Z(G) = ⊥`: then `F(G) ≤ Z(G) = ⊥`, but a minimal normal subgroup of a nontrivial group
  is abelian (`center_eq_top_of_isMinimalNormal_of_layer_eq_bot`, as `layer G = ⊥`), hence
  nilpotent normal, hence `≤ F(G) = ⊥` — impossible; so `G` is trivial.
* `⊥ < Z(G) < ⊤`: `Ḡ = G/Z(G)` is smaller with `F(Ḡ) = ⊥` (`fittingSubgroup_quotient_center_eq_bot`)
  and `layer Ḡ = ⊥` (`layer_quotient_center_eq_bot`); by induction `Ḡ` is solvable, and `G`
  is the extension of the abelian `Z(G)` by the solvable `Ḡ`. -/
private theorem isSolvable_aux : ∀ (n : ℕ) (G : Type u) [Group G] [Finite G],
    Nat.card G ≤ n → layer G = ⊥ → fittingSubgroup G ≤ Subgroup.center G → IsSolvable G := by
  intro n
  induction n with
  | zero => intro G _ _ hle _ _; exact absurd (Nat.card_pos.trans_le hle) (by simp)
  | succ m ih =>
    intro G _ _ hle hE hF
    by_cases hZtop : Subgroup.center G = ⊤
    · -- `Z(G) = ⊤`: `G` is abelian, hence solvable.
      refine isSolvable_of_comm (fun a b => ?_)
      have ha : a ∈ Subgroup.center G := hZtop ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    · by_cases hZbot : Subgroup.center G = ⊥
      · -- `F(G) ≤ Z(G) = ⊥`: a (necessarily abelian) minimal normal subgroup would lie in
        -- `F(G) = ⊥`; impossible, so `G` is trivial.
        rcases subsingleton_or_nontrivial G with hsub | _
        · exact isSolvable_of_subsingleton G
        · exfalso
          obtain ⟨M, hMnorm, hMne, hMmin⟩ := exists_isMinimalNormal (G := G)
          have hctr : Subgroup.center (M : Type _) = ⊤ :=
            center_eq_top_of_isMinimalNormal_of_layer_eq_bot hE ⟨hMnorm, hMne, hMmin⟩
          letI : CommGroup (M : Type _) := Group.commGroupOfCenterEqTop hctr
          have hMnil : Group.IsNilpotent (M : Type _) := CommGroup.isNilpotent
          have hMle : M ≤ fittingSubgroup G :=
            normal_nilpotent_le_fittingSubgroup M hMnorm hMnil
          exact hMne (le_bot_iff.mp ((hMle.trans hF).trans (le_of_eq hZbot)))
      · -- `⊥ < Z(G) < ⊤`: the quotient `G/Z(G)` is strictly smaller.
        have hcardlt : Nat.card (G ⧸ Subgroup.center G) < Nat.card G := by
          have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
          have h1 : 1 < Nat.card (Subgroup.center G) :=
            (Subgroup.center G).one_lt_card_iff_ne_bot.mpr hZbot
          have hqpos : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
          calc Nat.card (G ⧸ Subgroup.center G)
              < Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) := by
                exact lt_mul_of_one_lt_right hqpos h1
            _ = Nat.card G := hmul.symm
        haveI hsolvQ : IsSolvable (G ⧸ Subgroup.center G) :=
          ih (G ⧸ Subgroup.center G) (by omega)
            (layer_quotient_center_eq_bot G hE)
            (by rw [fittingSubgroup_quotient_center_eq_bot G hF]; exact bot_le)
        exact solvable_of_ker_le_range (Subgroup.center G).subtype
          (QuotientGroup.mk' (Subgroup.center G))
          (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

/-- **A finite group with no components and central Fitting subgroup is solvable.** The
order-bounded `isSolvable_aux` at `n = |G|`. This is the solvability hypothesis the
machine-checked solvable kernel needs; together they give Bender's central base case. -/
theorem isSolvable_of_layer_eq_bot_of_le_center (G : Type*) [Group G] [Finite G]
    (hE : layer G = ⊥) (hF : fittingSubgroup G ≤ Subgroup.center G) : IsSolvable G :=
  isSolvable_aux (Nat.card G) G le_rfl hE hF

/-- **The soluble base case of Bender's cornerstone (the irreducible kernel).** A
finite group with *no components* (`E(G) = 1`, i.e. `layer G = ⊥`) whose Fitting
subgroup is *central* (`F(G) ≤ Z(G)`) equals its Fitting subgroup: `F(G) = ⊤`.
Equivalently it is the soluble-type statement `C_G(F(G)) ≤ F(G)` restricted to the
central, component-free case — a finite group with no components and central `F(G)`
is nilpotent (indeed abelian, since `F(G) ≤ Z(G) ≤ F(G)` forces `G = F(G) = Z(G)`).

This is the one genuinely hard step the order-induction below cannot remove.

⚠️ **The `layer G = ⊥` hypothesis is essential and the previous formalization was
unsound without it.** A prior version of this axiom replaced `layer G = ⊥` with the
strictly weaker "all minimal normal subgroups are abelian"
(`∀ M, IsMinimalNormal M → center ↥M = ⊤`). That statement is *false*:
**`SL(2, 𝔽₅)`** (order 120) is a counterexample — its unique minimal normal subgroup
is the central `ℤ/2`, which is abelian, and `F(G) = Z(G) = ℤ/2`, so both the
"minimal normals abelian" and `F(G) ≤ Z(G)` hypotheses hold, yet `F(G) ≠ ⊤`. The
weaker form fails to exclude perfect central extensions of non-abelian simple groups
(`SL(2, 𝔽₅)` is a component of itself, so its `layer ≠ ⊥`). Aristotle (Harmonic's
auto-formalizer) found this counterexample on 2026-06-02; the `layer G = ⊥` form
restored here excludes `SL(2, 𝔽₅)` (whose layer is non-trivial). With `layer G = ⊥`,
`A₅` is likewise excluded (`layer A₅ = A₅ ≠ ⊥`).

The companion "no components ⟹ minimal normals abelian" half is a *theorem*
(`center_eq_top_of_isMinimalNormal_of_layer_eq_bot`, `MinimalNormal.lean`); it is a
genuine corollary of this kernel but cannot *replace* the `layer = ⊥` hypothesis (it
is one direction only).

**The axiom surface is now a single, sharp, clearly-true statement about the layer.**
Since the *solvable* case `[IsSolvable G] → F(G) ≤ Z(G) → F(G) = ⊤` is machine-checked
(`fittingSubgroup_eq_top_of_isSolvable_of_le_center`), solvability is the only missing
hypothesis. Solvability is then proved by strong induction on `|G|` (`isSolvable_aux`
below): the quotient `Ḡ = G/Z(G)` has `F(Ḡ) = ⊥` (`fittingSubgroup_quotient_center_eq_bot`,
the central-extension argument) and — by the *one* residual axiom
`layer_quotient_center_eq_bot` — also `layer Ḡ = ⊥`, so `Ḡ` is solvable by induction and
`G` is the extension of the abelian `Z(G)` by the solvable `Ḡ`. So Bender's cornerstone
now rests on exactly `layer_quotient_center_eq_bot`: *a central quotient of a
component-free group is component-free*. -/
theorem fittingSubgroup_eq_top_of_layer_eq_bot_of_le_center (G : Type*) [Group G] [Finite G]
    (hE : layer G = ⊥)
    (hF : fittingSubgroup G ≤ Subgroup.center G) :
    fittingSubgroup G = ⊤ :=
  have : IsSolvable G := isSolvable_of_layer_eq_bot_of_le_center G hE hF
  fittingSubgroup_eq_top_of_isSolvable_of_le_center G hF

/-- **Bender's central base case.** If `F*(G)` is central (`C_G(F*(G)) = ⊤`, i.e.
`F*(G) ≤ Z(G)`) then `F*(G) = ⊤`. A central `F*` makes the layer central, so it vanishes
(`layer_eq_bot_of_le_center`); the soluble kernel
(`fittingSubgroup_eq_top_of_layer_eq_bot_of_le_center`), applied with the now-trivial
layer and the central `F(G) ≤ F*(G) ≤ Z(G)`, gives `F(G) = ⊤`, hence
`F*(G) = E(G) ⊔ F(G) = ⊥ ⊔ ⊤ = ⊤`. -/
theorem genFittingSubgroup_eq_top_of_centralizer_eq_top (G : Type*) [Group G] [Finite G]
    (h : Subgroup.centralizer (genFittingSubgroup G : Set G) = ⊤) :
    genFittingSubgroup G = ⊤ := by
  have hcentral : genFittingSubgroup G ≤ Subgroup.center G :=
    SetLike.coe_subset_coe.mp (Subgroup.centralizer_eq_top_iff_subset.mp h)
  have hE : layer G = ⊥ :=
    layer_eq_bot_of_le_center (layer_le_genFittingSubgroup.trans hcentral)
  have hF : fittingSubgroup G = ⊤ :=
    fittingSubgroup_eq_top_of_layer_eq_bot_of_le_center G hE
      (fittingSubgroup_le_genFittingSubgroup.trans hcentral)
  rw [genFittingSubgroup, hE, hF, bot_sup_eq]

/-- Order-bounded form of Bender's cornerstone, proved by strong induction on `|G|`.
The induction step: let `C = C_G(F*(G))` (normal in `G`). If `C = ⊤` the central
base case (`genFittingSubgroup_eq_top_of_centralizer_eq_top`) finishes. Otherwise
`|C| < |G|`, so the inductive hypothesis applies to `C`; since `C` centralizes
`F*(G) ⊇ F*(C)` (`genFittingSubgroup_map_subtype_le`), every element of `C`
centralizes `F*(C)`, i.e. `C_C(F*(C)) = ⊤`, whence `F*(C) = ⊤` by induction, and so
`C = F*(C)·… ≤ F*(G)` by the same monotonicity. -/
private theorem bender_aux : ∀ (n : ℕ) (G : Type u) [Group G] [Finite G],
    Nat.card G ≤ n →
    Subgroup.centralizer (genFittingSubgroup G : Set G) ≤ genFittingSubgroup G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hle
    exact absurd (Nat.card_pos.trans_le hle) (by simp)
  | succ m ih =>
    intro G _ _ hle
    haveI : (genFittingSubgroup G).Normal := genFittingSubgroup_normal G
    by_cases hCtop : Subgroup.centralizer (genFittingSubgroup G : Set G) = ⊤
    · rw [hCtop, top_le_iff]
      exact genFittingSubgroup_eq_top_of_centralizer_eq_top G hCtop
    · -- `C` is a proper normal subgroup, so `|C| < |G|`.
      haveI hCnormal : (Subgroup.centralizer (genFittingSubgroup G : Set G)).Normal :=
        inferInstance
      set C := Subgroup.centralizer (genFittingSubgroup G : Set G) with hCdef
      have hcardlt : Nat.card C < Nat.card G := by
        refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ C.subtype_injective) ?_
        intro heq
        exact hCtop (Subgroup.eq_top_of_card_eq C heq)
      have hcardC : Nat.card C ≤ m := by omega
      -- Inductive hypothesis on `↥C`, plus `C_C(F*(C)) = ⊤`.
      have IHC := ih C hcardC
      have hCC : Subgroup.centralizer (genFittingSubgroup C : Set C) = ⊤ := by
        rw [eq_top_iff]
        intro c _
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        -- `y` lies in `F*(C)`, so `C.subtype y ∈ F*(G)`; `c ∈ C` centralizes `F*(G)`.
        have hyG : C.subtype y ∈ genFittingSubgroup G :=
          genFittingSubgroup_map_subtype_le (Subgroup.mem_map_of_mem _ hy)
        have hcG : (C.subtype c : G) ∈ C := c.2
        have hcomm : C.subtype y * C.subtype c = C.subtype c * C.subtype y :=
          (Subgroup.mem_centralizer_iff.mp hcG) _ hyG
        exact C.subtype_injective (by simpa [map_mul] using hcomm)
      rw [hCC, top_le_iff] at IHC
      -- `F*(C) = ⊤`, so `C ≤ F*(G)` by monotonicity.
      intro x hx
      have hxC : (⟨x, hx⟩ : C) ∈ genFittingSubgroup C := IHC ▸ Subgroup.mem_top _
      have := genFittingSubgroup_map_subtype_le (N := C) (Subgroup.mem_map_of_mem _ hxC)
      simpa using this

/-- **Bender's theorem — the cornerstone of the theory of the generalized Fitting
subgroup.** In any finite group, `F*(G)` is *self-centralizing*:
`C_G(F*(G)) ≤ F*(G)`. Equivalently `C_G(F*(G)) = Z(F*(G))`
(`centralizer_genFittingSubgroup_eq_center`).

This is what makes `F*(G)` the load-bearing object of the local theory: the action
of `G` on `F*(G)` by conjugation is faithful modulo the center, so
`G/Z(F*(G)) ↪ Aut(F*(G))` and the structure of `G` is controlled by `F*(G)`. It is
the generalized-Fitting analogue of the elementary fact `C_G(F(G)) ≤ F(G)` for
*soluble* `G`, extended past solubility by the layer.

**Proved** here by strong induction on `|G|` (`bender_aux`), resting only on the
central base case `genFittingSubgroup_eq_top_of_centralizer_eq_top` and the
normal-subgroup monotonicity `genFittingSubgroup_map_subtype_le`. The induction
marches the dependency down to the irreducible kernel: the bare assertion that a
finite group with central `F*` equals its `F*`. (Aschbacher, *Finite Group Theory*
31.13; Kurzweil-Stellmacher 6.5.8.) -/
theorem genFittingSubgroup_self_centralizing (G : Type*) [Group G] [Finite G] :
    Subgroup.centralizer (genFittingSubgroup G : Set G) ≤ genFittingSubgroup G :=
  bender_aux (Nat.card G) G le_rfl

/-- **`C_G(F*(G)) = Z(F*(G))`.** The centralizer of the generalized Fitting subgroup
is exactly its center, realized in `G` as `F*(G) ⊓ C_G(F*(G))`. The `≥` inclusion is
trivial; the `≤` inclusion is precisely Bender's cornerstone
(`genFittingSubgroup_self_centralizing`). -/
theorem centralizer_genFittingSubgroup_eq_center (G : Type*) [Group G] [Finite G] :
    Subgroup.centralizer (genFittingSubgroup G : Set G)
      = genFittingSubgroup G ⊓ Subgroup.centralizer (genFittingSubgroup G : Set G) :=
  (le_inf (genFittingSubgroup_self_centralizing G) le_rfl).antisymm inf_le_right

end FiniteSimpleGroups

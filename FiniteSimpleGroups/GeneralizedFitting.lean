import FiniteSimpleGroups.LayerNormal
import FiniteSimpleGroups.FittingSubgroup

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

/-- **Bender's cornerstone — the central base case (the irreducible kernel).** If
the generalized Fitting subgroup is *central* — its centralizer is everything,
`C_G(F*(G)) = ⊤`, equivalently `F*(G) ≤ Z(G)` — then `F*(G)` is the whole group.

This is the one genuinely hard step of Bender's theorem that the order-induction
below cannot remove: it is the assertion that a finite group whose generalized
Fitting subgroup is central must equal that subgroup (in particular be nilpotent).
Concretely `F*(G) ≤ Z(G)` forces `E(G) = 1` and `F(G) = Z(G)`, and the content is
that no *non-nilpotent* group can have its `F*` central — the generalized-Fitting
form of `C_G(F(G)) ≤ F(G)`. Recorded as an honest `axiom` (Aschbacher, *Finite Group
Theory* 31.13; Kurzweil-Stellmacher 6.5.8), strictly sharper than the full
self-centralizing statement, which is now *derived* from it
(`genFittingSubgroup_self_centralizing`) by induction on `|G|`. -/
axiom genFittingSubgroup_eq_top_of_centralizer_eq_top (G : Type*) [Group G] [Finite G]
    (h : Subgroup.centralizer (genFittingSubgroup G : Set G) = ⊤) :
    genFittingSubgroup G = ⊤

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

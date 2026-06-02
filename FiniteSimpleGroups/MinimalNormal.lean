import FiniteSimpleGroups.LayerNormal

/-!
# Minimal normal subgroups and the layer-structure step of Bender's soluble kernel

A **minimal normal subgroup** `M` of `G` is a nontrivial normal subgroup minimal among the
nontrivial normal subgroups. This file develops the elementary structure theory needed to
discharge the residual `(a)` of Bender's soluble kernel: *if `E(G) = ⊥` then every minimal
normal subgroup of `G` is abelian* (equivalently, a non-abelian minimal normal subgroup
yields a component, contradicting `layer = ⊥`).

The chain (all elementary — no deep classification):
* `IsMinimalNormal.eq_bot_or_eq_top_of_characteristic` — a minimal normal subgroup is
  **characteristically simple**: a characteristic subgroup of `↥M` is normal in `G`, lies in
  `M`, so by minimality is `⊥` or `M`.
* (next) a finite non-abelian characteristically simple group has a non-abelian minimal
  normal subgroup (socle argument); strong induction on `|G|` descends to a simple
  non-abelian subnormal subgroup, i.e. a component (`layer_ne_bot_of_normal_simple_factor`).
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

/-- `M` is a **minimal normal subgroup** of `G`: nontrivial, normal, and minimal among
nontrivial normal subgroups. -/
def IsMinimalNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≤ M → N = M

/-- **A minimal normal subgroup is characteristically simple.** A characteristic subgroup
`C` of `↥M` maps to a normal subgroup of `G` (`Subgroup.normal_of_characteristic_of_normal`)
contained in `M`; minimality forces `C.map M.subtype = ⊥` or `= M`, i.e. `C = ⊥` or `C = ⊤`
(the inclusion `M.subtype` is injective). -/
theorem IsMinimalNormal.eq_bot_or_eq_top_of_characteristic {M : Subgroup G}
    (hM : IsMinimalNormal M) {C : Subgroup (M : Type _)} (hC : C.Characteristic) :
    C = ⊥ ∨ C = ⊤ := by
  obtain ⟨hMnorm, _, hmin⟩ := hM
  haveI := hMnorm
  haveI := hC
  by_cases hCb : C = ⊥
  · exact Or.inl hCb
  · refine Or.inr ?_
    have hmapinj := Subgroup.map_injective (G := (M : Type _)) (N := G) M.subtype_injective
    have hCmapne : C.map M.subtype ≠ ⊥ := fun h => hCb (hmapinj (by rw [h, Subgroup.map_bot]))
    have heq : C.map M.subtype = M :=
      hmin _ inferInstance hCmapne (Subgroup.map_subtype_le C)
    refine hmapinj ?_
    rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **Distinct minimal normal subgroups intersect trivially.** `H ⊓ K` is normal and lies in
both; minimality of `H` forces it to be `⊥` or `H`, and `H` would give `H ≤ K`, hence `H = K`
by minimality of `K` — excluded. -/
theorem IsMinimalNormal.inf_eq_bot {H K : Subgroup G} (hH : IsMinimalNormal H)
    (hK : IsMinimalNormal K) (hne : H ≠ K) : H ⊓ K = ⊥ := by
  obtain ⟨hHnorm, _, hHmin⟩ := hH
  obtain ⟨hKnorm, hKbot, hKmin⟩ := hK
  haveI := hHnorm; haveI := hKnorm
  by_contra hbot
  have hHK : H ⊓ K = H := hHmin _ inferInstance hbot inf_le_left
  exact hne (hHK ▸ hKmin H hHnorm (fun h => hbot (h ▸ hHK)) (hHK ▸ inf_le_right))

/-- **Distinct minimal normal subgroups commute.** Both are normal, so `⁅H, K⁆ ≤ H ⊓ K = ⊥`
(`IsMinimalNormal.inf_eq_bot`, `commutator_le_inf`). -/
theorem IsMinimalNormal.commutator_eq_bot {H K : Subgroup G} (hH : IsMinimalNormal H)
    (hK : IsMinimalNormal K) (hne : H ≠ K) : ⁅H, K⁆ = ⊥ := by
  haveI := hH.1; haveI := hK.1
  exact le_bot_iff.mp ((Subgroup.commutator_le_inf H K).trans_eq (hH.inf_eq_bot hK hne))

end FiniteSimpleGroups

import FiniteSimpleGroups.GeneralizedFitting

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

/-- **A finite nontrivial group has a minimal normal subgroup.** The nontrivial normal
subgroups form a nonempty (`⊤`) collection in the well-founded (finite) subgroup lattice; a
`≤`-minimal element is a minimal normal subgroup. -/
theorem exists_isMinimalNormal [Finite G] [Nontrivial G] :
    ∃ M : Subgroup G, IsMinimalNormal M := by
  obtain ⟨M, hMP, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) ⟨⊤, inferInstance, top_ne_bot⟩
  exact ⟨M, hMP.1, hMP.2, fun N hNnorm hNbot hNle => le_antisymm hNle (hmin ⟨hNnorm, hNbot⟩ hNle)⟩

/-- **A characteristically simple non-abelian finite group has a non-abelian minimal normal
subgroup.** Phrased for `↥M` with `M` a minimal normal subgroup of `G` (so `↥M` is
characteristically simple). Such an `↥M` is *perfect* (the commutator subgroup is
characteristic, and `⊥` would make it abelian), hence its Fitting subgroup is trivial (`F = ⊤`
would make `↥M` nilpotent, so solvable, contradicting perfect + nontrivial). An abelian minimal
normal subgroup would be normal nilpotent, hence `≤ F = ⊥` — impossible. So the minimal normal
subgroup furnished by `exists_isMinimalNormal` is non-abelian. -/
theorem IsMinimalNormal.exists_nonabelian_sub {M : Subgroup G} [Finite G]
    (hM : IsMinimalNormal M) (hna : Subgroup.center (M : Type _) ≠ ⊤) :
    ∃ K : Subgroup (M : Type _), IsMinimalNormal K ∧ Subgroup.center (K : Type _) ≠ ⊤ := by
  haveI : Nontrivial (M : Type _) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hna (eq_top_iff.mpr fun x _ =>
      Subgroup.mem_center_iff.mpr fun g => Subsingleton.elim _ _)
  -- commutator `= ⊥` would make `↥M` abelian; rule it out via `hna`.
  have hbot_imp : commutator (M : Type _) = ⊥ → False := by
    intro h
    refine hna (eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => ?_)
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top x)) g (Subgroup.mem_top g)
  -- `↥M` is perfect.
  have hperf : Group.IsPerfect (M : Type _) := by
    rw [Group.isPerfect_def]
    rcases hM.eq_bot_or_eq_top_of_characteristic (C := commutator (M : Type _)) inferInstance
      with h | h
    · exact absurd h hbot_imp
    · exact h
  haveI := hperf
  -- The Fitting subgroup of `↥M` is trivial.
  have hF : fittingSubgroup (M : Type _) = ⊥ := by
    rcases hM.eq_bot_or_eq_top_of_characteristic (fittingSubgroup_characteristic (M : Type _))
      with h | h
    · exact h
    · haveI : Group.IsNilpotent (M : Type _) :=
        (fittingSubgroup_eq_top_iff_isNilpotent (M : Type _)).mp h
      exact absurd IsNilpotent.to_isSolvable (Group.IsPerfect.not_isSolvable (M : Type _))
  -- A minimal normal subgroup of `↥M`; it must be non-abelian.
  obtain ⟨K, hK⟩ := exists_isMinimalNormal (G := (M : Type _))
  refine ⟨K, hK, fun hKab => ?_⟩
  haveI := hK.1
  have hKnil : Group.IsNilpotent (K : Type _) :=
    ⟨1, (upperCentralSeries_one (K : Type _)).trans hKab⟩
  exact hK.2.1 (le_bot_iff.mp
    (hF ▸ normal_nilpotent_le_fittingSubgroup K hK.1 hKnil))

end FiniteSimpleGroups

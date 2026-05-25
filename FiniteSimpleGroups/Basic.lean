import Mathlib

/-!
# Basic definitions for finite simple groups

A **finite simple group** is a group `G` such that
* `G` is finite,
* `G` is nontrivial (otherwise the simplicity condition is vacuous and the
  trivial group is conventionally excluded from "simple group" lists),
* the only normal subgroups of `G` are `{1}` and `G` itself.

Mathlib's `IsSimpleGroup` already captures the third condition. We bundle the
finiteness + nontriviality requirements into a single typeclass `IsFSG` for
readability throughout this scaffold.

The big question of CFSG: enumerate all such `G` up to isomorphism. See
`FiniteSimpleGroups.Classification` for the answer.
-/

namespace FiniteSimpleGroups

/-- A **Finite Simple Group**: nontrivial, finite, with no proper nontrivial
normal subgroup. The conventional CFSG-subject definition. -/
class IsFSG (G : Type*) [Group G] : Prop where
  finite : Finite G
  nontrivial : Nontrivial G
  simple : IsSimpleGroup G

attribute [instance] IsFSG.finite IsFSG.nontrivial IsFSG.simple

/-- Trivial group is **not** an `IsFSG` by convention. -/
example : ¬ IsFSG PUnit := by
  intro h
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) h.nontrivial

end FiniteSimpleGroups

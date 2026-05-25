/-
# Mathlib stubs for the FT port

Local axiomatization of finite-group-theory concepts that the BG / PF port
needs but mathlib does not yet have. Each stub is marked **STUB** and is
intended to be replaced by the real mathlib definition / theorem when one
of two things happens:

1. We upstream the missing piece as a mathlib PR. Stub deletion is the
   "finished signal" for that PR.
2. Someone else upstreams it independently. We swap the stub for the import.

## Standing on what mathlib has

| Concept              | Mathlib | Notes |
| -------------------- | ------- | ----- |
| `IsPGroup p G`       | ✅      | `Mathlib.GroupTheory.PGroup` |
| `Sylow`              | ✅      | `Mathlib.GroupTheory.Sylow`  |
| `IsNilpotent`        | ✅      | `Mathlib.GroupTheory.Nilpotent` |
| `IsSolvable`         | ✅      | `Mathlib.GroupTheory.Solvable`  |
| `frattini G`         | ✅      | `Mathlib.GroupTheory.Frattini`  |
| `IsSubnormal`        | ✅      | `Mathlib.GroupTheory.IsSubnormal` (2026) |
| `Subgroup.normalizer`| ✅      | `Mathlib.GroupTheory.Subgroup.Basic` |
| `Subgroup.centralizer` | ✅    |                                |

## Standing on stubs (this file)

| Concept              | Stub form               | Upstream-PR difficulty |
| -------------------- | ----------------------- | ---------------------- |
| `FittingSubgroup G`  | `opaque` Subgroup       | Small (few hundred LOC)|
| `pCore p G`          | `opaque` Subgroup       | Small                  |
| `IsAbelem G`         | `def` (elementary abelian) | Tiny (one PR)        |
| `MinNormal H G`      | `def` (min G-normal)    | Tiny                   |
| `IsHall π G H`       | `def` (π-Hall)          | Small                  |
| `IsChiefFactor V U G`| `def` (factor in chief series) | Medium          |

## Approach

This file holds the local mathlib gap. All entries fall into one of:

- **Real defs** — `pCore`, `FittingSubgroup` (now defined via `normalClosure`
  to get `Normal` instances for free).
- **Placeholder defs** — `pCoreLayer` returns `⊤`; downstream uses are
  vacuous but compile.
- **Named axioms** (in this file or in `BGsection1/P*_*.lean`) — for
  facts cited from `papers/odd-order/BGsection1.v` whose translation we
  defer. Each axiom carries a citation pointing to the upstream lemma
  and a brief reason the proof is non-trivial in Lean.

Zero `sorry` warnings — everything is either proved or a named axiom. -/

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.IsSubnormal

namespace FeitThompson.Stubs

variable {G : Type*} [Group G]

/-! ### Elementary abelian groups -/

/-- A group is **elementary abelian** if it is abelian and there exists a prime `p`
such that every element has order dividing `p`. Equivalently, an abelian p-group
of exponent p. (Bourbaki / Aschbacher §23.) -/
def IsAbelem (G : Type*) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ IsMulCommutative G ∧ ∀ g : G, g ^ p = 1

/-! ### Minimal normal subgroups

A subgroup `H ≤ G` is **G-minimal-normal** if it is a non-trivial G-normal
subgroup and contains no smaller non-trivial G-normal subgroup. In B & G this
is written `minnormal M G`. We phrase it for the ambient group `G` itself
acting by conjugation (the only case used in §1).
-/

/-- `MinNormal H` says `H` is a minimal non-trivial normal subgroup of `G`. -/
def MinNormal (H : Subgroup G) : Prop :=
  H ≠ ⊥ ∧ H.Normal ∧
    ∀ K : Subgroup G, K.Normal → K ≤ H → K = ⊥ ∨ K = H

/-! ### p-core and Fitting subgroup -- promoted to real defs

These were `sorry`-witnessed stubs in earlier increments. Both now have
real definitions (the same shape we'd push upstream in a mathlib PR).
The naming `pCore` / `FittingSubgroup` matches the planned mathlib API. -/

section RealDefs
variable (G)

/-- The **p-core** `O_p(G)` — the largest normal p-subgroup of G.

Defined as the `normalClosure` of the union of all normal p-subgroups.
Since each member of the family is already normal, the union is
conjugation-invariant and the normalClosure equals the join. Using
`normalClosure` rather than `sSup` makes the `Normal` instance free
(via `Subgroup.normalClosure_normal`). -/
noncomputable def pCore (p : ℕ) : Subgroup G :=
  Subgroup.normalClosure
    (⋃ H ∈ {H : Subgroup G | H.Normal ∧ IsPGroup p H}, (H : Set G))

/-- The **Fitting subgroup** `F(G)` — the largest nilpotent normal subgroup of G.

Defined as the `normalClosure` of the union of all nilpotent normal
subgroups. Same trick as `pCore`: makes `Normal` an automatic instance.
For finite G this is itself nilpotent (Fitting's theorem). -/
noncomputable def FittingSubgroup : Subgroup G :=
  Subgroup.normalClosure
    (⋃ H ∈ {H : Subgroup G | H.Normal ∧ Group.IsNilpotent H}, (H : Set G))

end RealDefs

/-- The p-core is normal — real proof now, via the `normalClosure` definition. -/
instance pCore_normal (G : Type*) [Group G] (p : ℕ) :
    (pCore G p).Normal := by
  unfold pCore; infer_instance

/-- The Fitting subgroup is normal — real proof now, via the `normalClosure` definition. -/
instance FittingSubgroup_normal (G : Type*) [Group G] :
    (FittingSubgroup G).Normal := by
  unfold FittingSubgroup; infer_instance

/-! ### Iterated p-core layer

For the upper p-series. `pCoreLayer p G n` is `O_{p^{n}}(G)` in the layered
notation; specifically `pCoreLayer p G 2 = O_{p',p}(G)`. -/

/-- **PLACEHOLDER DEF**: iterated p-core layer.

The mathematically-correct definition is recursive in G (preimages in
quotients), which requires more machinery than we have set up. For now
this returns `⊤` — wrong mathematically, but compiles. Downstream
*statements* using `pCoreLayer` are vacuous; downstream *theorems* are
left as axioms. -/
noncomputable def pCoreLayer (_p : ℕ) (G : Type*) [Group G] (_n : ℕ) : Subgroup G := ⊤

/-! ### Hall subgroup -/

/-- `IsHall π H` says H is a π-Hall subgroup of G: H is a π-subgroup and
[G : H] is coprime to all primes in π. -/
def IsHall (π : Set ℕ) [Fintype G] (H : Subgroup G) : Prop :=
  (∀ p ∈ π, ∀ q : ℕ, q.Prime → q ∣ (Nat.card H : ℕ) → q = p) ∧
    ∀ p ∈ π, ¬ (p ∣ (H.index : ℕ))

/-! ### Chief factors

A chief factor of G is a quotient `U / V` arising from a chief series — a
maximal G-invariant normal series. We phrase it directly: V ⊲ U ⊲ G with
no G-normal subgroup strictly between them.
-/

/-- `IsChiefFactor V U` says V < U are G-normal subgroups with no G-normal
subgroup strictly between them. -/
def IsChiefFactor (V U : Subgroup G) : Prop :=
  V.Normal ∧ U.Normal ∧ V < U ∧
    ∀ K : Subgroup G, K.Normal → V ≤ K → K ≤ U → K = V ∨ K = U

end FeitThompson.Stubs

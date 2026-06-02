import FiniteSimpleGroups.ComponentStructure

/-!
# Aschbacher 31.4 — the component-vs-subnormal dichotomy, join-free

For a component `L` and a subnormal subgroup `H`, either `L ≤ H` or `⁅L, H⁆ = ⊥`.

The classical proof of this (Aschbacher, *Finite Group Theory*, 31.4) runs through the
normal closure `⟨L^H⟩` and so is usually presented on top of **Wielandt's subnormal-join
theorem**. This file proves it **without the join**: the centralizing in the awkward
"`H ∩ L` is central in `L`" case is propagated by a *forward* induction along `H`'s
subnormal chain (`centralizing_by_subnormal`), where at each step `M ◁ J` the containment
`⁅L, H ⊓ J⁆ ≤ H ⊓ M` (`commutator_le_inf_of_normalStep`) combines with the three-subgroups
lemma and the perfectness `⁅L, L⁆ = L` of the quasisimple component.

This proof was found by Harmonic's Aristotle (project `adf60350`, 2026-06-02) on a
self-contained statement and ported here; the original is preserved verbatim in
`aristotle-solution-components-commute.lean`. The surprise: the repository's earlier
assumption that this needed `IsSubnormal.sup` was too pessimistic — the dichotomy is
axiom-free.
-/

namespace FiniteSimpleGroups

variable {G : Type*} [Group G]

open Subgroup

/-- Forward induction along a `ReflTransGen` chain from `a` to `b`. -/
private lemma reflTransGen_forward {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) {P : α → Prop}
    (base : P a) (step : ∀ c d, r c d → Relation.ReflTransGen r d b → P c → P d) :
    P b := by
  have := h.head_induction_on (motive := fun x _ => P x → P b)
    (fun pb => pb)
    (fun {c d} rcd hdb ih pc => ih (step c d rcd hdb pc))
  exact this base

/-- Restricting a subnormal chain by intersecting with `K`. -/
private lemma isSubnormal_restrict {L M K : Subgroup G}
    (h : IsSubnormal L M) (hK : K ≤ M) : IsSubnormal (L ⊓ K) K := by
  refine h.head_induction_on (motive := fun J _ => IsSubnormal (J ⊓ K) K) ?base ?step
  case base =>
    show IsSubnormal (M ⊓ K) K
    rw [inf_eq_right.mpr hK]
  case step =>
    intro J J' hJJ' _ ih
    show IsSubnormal (J ⊓ K) K
    apply Relation.ReflTransGen.head _ (show IsSubnormal (J' ⊓ K) K from ih)
    refine ⟨inf_le_inf_right K hJJ'.1, ?_⟩
    constructor
    intro ⟨x, hx_J'K⟩
    have hx_J'K' := hx_J'K
    rw [Subgroup.mem_inf] at hx_J'K
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    intro ⟨hx_J, hx_K⟩ ⟨g, hg_J'K⟩
    have hg_J'K' := hg_J'K
    rw [Subgroup.mem_inf] at hg_J'K
    constructor
    · have hmem : (⟨x, hx_J'K'.1⟩ : ↥J') ∈ J.subgroupOf J' := by
        rw [Subgroup.mem_subgroupOf]; exact hx_J
      have := hJJ'.2.conj_mem _ hmem ⟨↑g, hg_J'K.1⟩
      rwa [Subgroup.mem_subgroupOf] at this
    · exact K.mul_mem (K.mul_mem hg_J'K.2 hx_K) (K.inv_mem hg_J'K.2)

/-- If `L` is subnormal in `⊤` and `L ≤ K`, then `L` is subnormal in `K`. -/
private lemma isSubnormal_of_le {L K : Subgroup G}
    (h : IsSubnormal L ⊤) (hLK : L ≤ K) : IsSubnormal L K := by
  have := isSubnormal_restrict h (le_top : K ≤ ⊤)
  rwa [inf_eq_left.mpr hLK] at this

/-- A perfect subgroup satisfies `⁅L, L⁆ = L` as subgroups of the ambient group. -/
private lemma perfect_commutator_eq_self {L : Subgroup G}
    (hperf : commutator L = ⊤) : ⁅L, L⁆ = L := by
  have map_top : (⊤ : Subgroup L).map L.subtype = L := by
    ext x; constructor
    · rintro ⟨y, _, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have key : ⁅L, L⁆ = (⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆).map L.subtype := by
    rw [Subgroup.map_commutator, map_top]
  change ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ at hperf
  rw [key, hperf, map_top]

/-- If `H` is normal in `K` (IsNormalStep) and `L ≤ K`, then `H ⊓ L` is normal in `L`
(in the `subgroupOf` sense). -/
private lemma inf_subgroupOf_normal_of_normalStep {H K L : Subgroup G}
    (hHK : IsNormalStep H K) (hLK : L ≤ K) :
    ((H ⊓ L).subgroupOf L).Normal := by
  constructor
  intro ⟨x, hxL⟩ hxHL g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hxHL ⊢
  constructor
  · have hgK : (↑g : G) ∈ K := hLK g.2
    have hxK : (↑x : G) ∈ K := hLK hxL
    have hmem : (⟨x, hxK⟩ : ↥K) ∈ H.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]; exact hxHL.1
    have := hHK.2.conj_mem _ hmem ⟨↑g, hgK⟩
    rwa [Subgroup.mem_subgroupOf] at this
  · exact L.mul_mem (L.mul_mem g.2 hxL) (L.inv_mem g.2)

/-- Key containment: if `L ≤ M`, `IsNormalStep M J`, `IsNormalStep H K`, `J ≤ K`, then
`⁅L, H ⊓ J⁆ ≤ H ⊓ M`. Elements `[l, h]` land in `M` (normality of `M` in `J`) and in `H`
(normality of `H` in `K`). -/
private lemma commutator_le_inf_of_normalStep {L H M J K : Subgroup G}
    (hLM : L ≤ M) (hMJ : IsNormalStep M J)
    (hHK : IsNormalStep H K) (hJK : J ≤ K) :
    ⁅L, H ⊓ J⁆ ≤ H ⊓ M := by
  rw [Subgroup.commutator_le]
  intro l hl h hh
  rw [Subgroup.mem_inf] at hh ⊢
  have hlM := hLM hl; have hlJ := hMJ.1 hlM; have hlK := hJK hlJ
  have hhH := hh.1; have hhJ := hh.2; have hhK := hJK hhJ
  constructor
  · have : (⟨h, hhK⟩ : ↥K) ∈ H.subgroupOf K := by rwa [Subgroup.mem_subgroupOf]
    have := hHK.2.conj_mem _ this ⟨l, hlK⟩
    rw [Subgroup.mem_subgroupOf] at this
    show l * h * l⁻¹ * h⁻¹ ∈ H
    exact H.mul_mem this (H.inv_mem hhH)
  · have : (⟨l⁻¹, hMJ.1 (M.inv_mem hlM)⟩ : ↥J) ∈ M.subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]; exact M.inv_mem hlM
    have := hMJ.2.conj_mem _ this ⟨h, hhJ⟩
    rw [Subgroup.mem_subgroupOf] at this
    show l * h * l⁻¹ * h⁻¹ ∈ M
    rw [show l * h * l⁻¹ * h⁻¹ = l * (h * l⁻¹ * h⁻¹) from by group]
    exact M.mul_mem hlM this

/-- Three-subgroups lemma + perfectness: if `⁅L, L⁆ = L` and `⁅⁅L, H⁆, L⁆ = ⊥`,
then `⁅L, H⁆ = ⊥`. -/
private lemma commutator_eq_bot_of_perfect_comm {L H : Subgroup G}
    (hperf : ⁅L, L⁆ = L) (h : ⁅⁅L, H⁆, L⁆ = ⊥) :
    ⁅L, H⁆ = ⊥ := by
  have h2 : ⁅⁅H, L⁆, L⁆ = ⊥ := by rwa [Subgroup.commutator_comm H L]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h h2
  rwa [hperf] at h3

/-- Bridge: `(H ⊓ L).subgroupOf L ≤ center ↥L` implies `⁅L, H ⊓ L⁆ = ⊥`. -/
private lemma commutator_eq_bot_of_subgroupOf_le_center {L H : Subgroup G}
    (hcent : (H ⊓ L).subgroupOf L ≤ Subgroup.center L) :
    ⁅L, H ⊓ L⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro l hl h hh
  rw [Subgroup.mem_inf] at hh; rw [Subgroup.mem_bot]
  have hmem : (⟨h, hh.2⟩ : ↥L) ∈ (H ⊓ L).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]; exact hh
  have := (Subgroup.mem_center_iff.mp (hcent hmem)) ⟨l, hl⟩
  have hcomm : l * h = h * l := by have := congr_arg Subtype.val this; simpa using this
  rw [commutatorElement_def]
  calc l * h * l⁻¹ * h⁻¹ = (l * h) * (l * h)⁻¹ := by rw [hcomm]; group
    _ = 1 := mul_inv_cancel _

/-- `(H ⊓ L).subgroupOf L = ⊤` implies `L ≤ H`. -/
private lemma le_of_subgroupOf_eq_top {L H : Subgroup G}
    (h : (H ⊓ L).subgroupOf L = ⊤) : L ≤ H := by
  intro x hx
  have : (⟨x, hx⟩ : ↥L) ∈ (H ⊓ L).subgroupOf L := by rw [h]; trivial
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at this; exact this.1

/-- Centralizing propagates along the subnormal chain (the join-free heart): if `L ◁◁ K`,
`H ◁ K`, `⁅L, L⁆ = L`, and `⁅L, H ⊓ L⁆ = ⊥`, then `⁅L, H⁆ = ⊥`. Forward induction: at each
step `M ◁ J`, `⁅L, H ⊓ J⁆ ≤ H ⊓ M`, and three-subgroups + perfectness gives
`⁅L, H ⊓ J⁆ = ⊥` from `⁅L, H ⊓ M⁆ = ⊥`. -/
private lemma centralizing_by_subnormal {L K H : Subgroup G}
    (hsub : IsSubnormal L K) (hHK : IsNormalStep H K)
    (hperf : ⁅L, L⁆ = L) (hbase : ⁅L, H ⊓ L⁆ = ⊥) :
    ⁅L, H⁆ = ⊥ := by
  suffices h : ⁅L, H ⊓ K⁆ = ⊥ by
    rwa [inf_eq_left.mpr hHK.1] at h
  exact (reflTransGen_forward hsub
    (P := fun J => L ≤ J ∧ J ≤ K ∧ ⁅L, H ⊓ J⁆ = ⊥)
    ⟨le_refl L, hsub.le, hbase⟩
    (fun M J hMJ hJK ⟨hLM, _, hIH⟩ => by
      have hJK' : J ≤ K := le_trans (IsSubnormal.le hJK) le_rfl
      refine ⟨le_trans hLM hMJ.1, hJK', ?_⟩
      have hle : ⁅L, H ⊓ J⁆ ≤ H ⊓ M :=
        commutator_le_inf_of_normalStep hLM hMJ hHK hJK'
      have hcomm : ⁅⁅L, H ⊓ J⁆, L⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact le_bot_iff.mp (le_trans (Subgroup.commutator_mono le_rfl hle) (le_of_eq hIH))
      exact commutator_eq_bot_of_perfect_comm hperf hcomm)).2.2

/-- **Aschbacher 31.4** (component-vs-subnormal dichotomy): a component `L` and a
subnormal subgroup `H` satisfy `L ≤ H` or `⁅L, H⁆ = ⊥`. **Axiom-free** (no Wielandt
join). Induction on the subnormal chain of `H`. -/
theorem IsComponent.subnormal_dichotomy {L H : Subgroup G}
    (hL : IsComponent L) (hH : IsSubnormal H ⊤) :
    L ≤ H ∨ ⁅L, H⁆ = ⊥ := by
  haveI := hL.isQuasisimple
  induction hH using Relation.ReflTransGen.head_induction_on with
  | refl => left; exact le_top
  | head hHK _hKT ih =>
    rcases ih with hLK | hLK_bot
    · have hN := inf_subgroupOf_normal_of_normalStep hHK hLK
      rcases IsQuasisimple.normal_le_center_or_eq_top hN with hcent | htop
      · right
        have hperf := perfect_commutator_eq_self (IsQuasisimple.commutator_eq_top L)
        have hbase := commutator_eq_bot_of_subgroupOf_le_center hcent
        have hsub := isSubnormal_of_le hL.isSubnormal hLK
        exact centralizing_by_subnormal hsub hHK hperf hbase
      · left; exact le_of_subgroupOf_eq_top htop
    · right
      exact le_bot_iff.mp (le_trans (Subgroup.commutator_mono le_rfl hHK.1) (le_of_eq hLK_bot))

end FiniteSimpleGroups

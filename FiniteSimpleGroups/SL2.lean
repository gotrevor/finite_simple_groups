import Mathlib
import FiniteSimpleGroups.LieType
import FiniteSimpleGroups.PSLIwasawa
import FiniteSimpleGroups.SL2Card
import FiniteSimpleGroups.SLnAction
import FiniteSimpleGroups.SLnIwasawa

/-!
# `PSL(2,q)` is simple for prime `q ≥ 4` — all Iwasawa obligations, machine-checked

`PSLIwasawa.lean` reduces `PSL_isSimpleGroup` for `PSL 2 q` (an `axiom` in
`LieType.lean`) to the Iwasawa obligations. This file **discharges all of
them** — from scratch and fully axiom-free — and assembles `PSL2_isSimpleGroup`:

* `SL2_perfect` : `commutator (SL(2,F)) = ⊤` for any field with `4 ≤ |F|`.
* `PSL2_perfect` : `commutator (PSL 2 q) = ⊤` for `q` prime with `4 ≤ q`
  (the Iwasawa "perfect" obligation).
* `PSL2_nontrivial` : `Nontrivial (PSL 2 q)` for every prime `q`
  (the Iwasawa `Nontrivial` obligation).

* `psl1Action` : `MulAction (PSL 2 q) ℙ¹(F_q)` (the Iwasawa `MulAction`
  obligation), built from the linear `SL(2,F)` action on `Fin 2 → F` descended
  through the center (which fixes every line, `center_smul_eq`).

* `pslFaithful` : `FaithfulSMul (PSL 2 q) ℙ¹(F_q)` (the Iwasawa `FaithfulSMul`
  obligation). The kernel of the `SL(2,q)` action on `ℙ¹` is exactly the center
  (`ker_le_center`, the converse of `center_le_ker`), so the descended hom
  `pslPermHom : PSL(2,q) → Sym(ℙ¹)` is injective.

* `pslQuasiPreprimitive` : `IsQuasiPreprimitive (PSL 2 q) ℙ¹(F_q)` (the Iwasawa
  `IsQuasiPreprimitive` obligation), from 2-transitivity of `PSL(2,q)` on `ℙ¹`
  (`psl_two_trans`/`psl_two_pretrans`): a 2-transitive action is primitive, hence
  quasi-preprimitive. The geometric core (`exists_sl2_maps_ref`) carries the
  reference frame `([e₁],[e₂])` to any pair of distinct lines.

* `pslIwasawa` : the unipotent `IwasawaStructure` — the family `Tline x`
  (image in `PSL` of the transvection subgroup along the line `x`), each abelian,
  conjugation-equivariant (`Tline_conj`, from `transSL_conj`), and generating
  (`Tline_iSup`, via `transvections_generate`).

All **six** pieces feeding `PSL2_isSimpleGroup_of_iwasawa` are thus
machine-checked here. They assemble into

* `PSL2_isSimpleGroup` : `IsSimpleGroup (PSL 2 q)` for every prime `q ≥ 4`,
  `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`).

This **discharges the deep CFSG `axiom PSL_isSimpleGroup` at `n = 2`** (the one
tractable family case). See `PENDING_WORK §D`.

Mathlib v4.29.1 has `PSL`/`SL` and the transvection machinery but **no** SL(2)
perfectness and **no** PSL simplicity, so this is genuine new content, consistent
with the repository's "one rule" (never re-derive what mathlib already has).

## Proof outline

The two elementary transvection families `upper t = !![1,t;0,1]` and
`lower t = !![1,0;t,1]` generate `SL(2,F)` (`transvections_generate`, via the
direct Bruhat decomposition for `2×2` matrices and the Steinberg identity
`diagSL_eq` writing `diag(a,a⁻¹)` as a product of transvections). Each
transvection is a commutator: the diagonal-conjugation identity
`⁅diag(a,a⁻¹), upper s⁆ = upper((a²−1)s)` (`comm_diag_upper`, and the `lower`
analogue) makes `s ↦ (a²−1)s` surjective once `a² ≠ 1`, which holds for some
`a ≠ 0` when `|F| ≥ 4` (`exists_sq_ne_one`). Hence the commutator subgroup
contains a generating set, so it is `⊤`. Perfectness then descends to the
quotient `PSL(2,q) = SL(2,q)/Z` (`perfect_of_surjective`).
-/

namespace FiniteSimpleGroups
namespace SL2

open Matrix
open SLn
open scoped commutatorElement
open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

/-- The upper elementary transvection `!![1, t; 0, 1]` in `SL(2,F)`. -/
def upper (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower elementary transvection `!![1, 0; t, 1]` in `SL(2,F)`. -/
def lower (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem upper_val (t : F) : (upper t).val = !![1, t; 0, 1] := rfl
@[simp] theorem lower_val (t : F) : (lower t).val = !![1, 0; t, 1] := rfl

/-- The diagonal `SL₂` element `diag(a, a⁻¹)`. -/
def diagSL (a : F) (ha : a ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, mul_inv_cancel₀ ha]⟩

@[simp] theorem diagSL_val (a : F) (ha : a ≠ 0) : (diagSL a ha).val = !![a, 0; 0, a⁻¹] := rfl

/-- **Steinberg diagonal identity:** `diag(a,a⁻¹)` is a product of transvections. -/
theorem diagSL_eq (a : F) (ha : a ≠ 0) :
    diagSL a ha =
      upper a * lower (-a⁻¹) * upper a * upper (-1) * lower 1 * upper (-1) := by
  apply Subtype.ext
  simp only [diagSL, SpecialLinearGroup.coe_mul, upper_val, lower_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- The generating set: upper and lower transvections. -/
def S : Set (SpecialLinearGroup (Fin 2) F) :=
  Set.range (upper (F := F)) ∪ Set.range (lower (F := F))

theorem upper_mem_closure (t : F) : upper t ∈ Subgroup.closure (S (F := F)) :=
  Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)

theorem lower_mem_closure (t : F) : lower t ∈ Subgroup.closure (S (F := F)) :=
  Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)

theorem diagSL_mem_closure (a : F) (ha : a ≠ 0) :
    diagSL a ha ∈ Subgroup.closure (S (F := F)) := by
  rw [diagSL_eq a ha]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (upper_mem_closure a) (lower_mem_closure _)) (upper_mem_closure a))
    (upper_mem_closure _)) (lower_mem_closure 1)) (upper_mem_closure _)

/-- Bruhat decomposition, `c ≠ 0`: `!![a,b;c,d] = upper((a-1)/c)·lower c·upper((d-1)/c)`. -/
theorem mk_eq_c_ne (a b c d : F) (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    (h : (!![a, b; c, d]).det = 1) :
    (⟨!![a, b; c, d], h⟩ : SpecialLinearGroup (Fin 2) F)
      = upper ((a - 1) / c) * lower c * upper ((d - 1) / c) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, upper_val, lower_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring) <;>
    (try linear_combination hdet) <;> (try linear_combination -hdet)

/-- Bruhat decomposition, `c = 0`: `!![a,b;0,d] = diag(a,a⁻¹)·upper(b·a⁻¹)`. -/
theorem mk_eq_c_eq (a b d : F) (hdet : a * d - b * 0 = 1)
    (h : (!![a, b; 0, d]).det = 1) :
    ∃ ha : a ≠ 0,
      (⟨!![a, b; 0, d], h⟩ : SpecialLinearGroup (Fin 2) F) = diagSL a ha * upper (b * a⁻¹) := by
  rw [mul_zero, sub_zero] at hdet
  have ha : a ≠ 0 := by rintro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  refine ⟨ha, ?_⟩
  apply Subtype.ext
  simp only [diagSL, SpecialLinearGroup.coe_mul, upper_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> (try ring) <;>
    (try linear_combination hdet) <;> (try linear_combination -hdet)

/-- **The elementary transvections generate `SL(2,F)`.** -/
theorem transvections_generate :
    Subgroup.closure (S (F := F)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  induction g using SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
    by_cases hc : c = 0
    · subst hc
      obtain ⟨ha, hg⟩ := mk_eq_c_eq a b d hdet _
      rw [hg]
      exact mul_mem (diagSL_mem_closure a ha) (upper_mem_closure _)
    · rw [mk_eq_c_ne a b c d hdet hc _]
      exact mul_mem (mul_mem (upper_mem_closure _) (lower_mem_closure _)) (upper_mem_closure _)

/-! ### Commutator identities and perfectness -/

@[simp] theorem upper_mul (s t : F) : upper s * upper t = upper (s + t) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, upper_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;> ring

theorem upper_inv (s : F) : (upper s)⁻¹ = upper (-s) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, upper_val, SpecialLinearGroup.coe_one,
      Matrix.mul_fin_two, Fin.sum_univ_two, Matrix.one_fin_two] <;> ring

theorem lower_inv (s : F) : (lower s)⁻¹ = lower (-s) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, lower_val, SpecialLinearGroup.coe_one,
      Matrix.mul_fin_two, Fin.sum_univ_two, Matrix.one_fin_two] <;> ring

theorem diagSL_inv (a : F) (ha : a ≠ 0) :
    (diagSL a ha)⁻¹ = diagSL a⁻¹ (inv_ne_zero ha) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, diagSL_val, SpecialLinearGroup.coe_one,
      Matrix.mul_fin_two, Fin.sum_univ_two, Matrix.one_fin_two] <;>
    (try field_simp)

/-- `⁅diag(a,a⁻¹), upper s⁆ = upper((a²-1)·s)`. -/
theorem comm_diag_upper (a : F) (ha : a ≠ 0) (s : F) :
    ⁅diagSL a ha, upper s⁆ = upper ((a ^ 2 - 1) * s) := by
  rw [commutatorElement_def, upper_inv, diagSL_inv a ha]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, diagSL_val, upper_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> ring

/-- `⁅diag(a,a⁻¹), lower s⁆ = lower((a⁻²-1)·s)`. -/
theorem comm_diag_lower (a : F) (ha : a ≠ 0) (s : F) :
    ⁅diagSL a ha, lower s⁆ = lower ((a⁻¹ ^ 2 - 1) * s) := by
  rw [commutatorElement_def, lower_inv, diagSL_inv a ha]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, diagSL_val, lower_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Fin.sum_univ_two] <;>
    (try field_simp) <;> ring

/-- For a field with `4 ≤ |F|`, some `a` has `a ≠ 0` and `a² ≠ 1`. -/
theorem exists_sq_ne_one [Fintype F] (hF : 4 ≤ Fintype.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h1 : a ^ 2 = 1 := h a ha
      have : a = 1 ∨ a = -1 := by rw [sq] at h1; exact mul_self_eq_one_iff.mp h1
      rcases this with h2 | h2 <;> simp [h2]
  have hcard : Fintype.card F ≤ 3 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    refine this.trans ?_
    calc ({0, 1, -1} : Finset F).card
        ≤ ({1, -1} : Finset F).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({-1} : Finset F).card + 1) + 1 := by gcongr; exact Finset.card_insert_le _ _
      _ ≤ 3 := by simp
  omega

/-- **`SL(2,F)` is perfect when `4 ≤ |F|`.** -/
theorem SL2_perfect [Fintype F] (hF : 4 ≤ Fintype.card F) :
    commutator (SpecialLinearGroup (Fin 2) F) = ⊤ := by
  obtain ⟨a, ha, ha2⟩ := exists_sq_ne_one hF
  have hunit : a ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ha2
  have hunit' : a⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [sub_ne_zero, inv_pow, ne_eq, inv_eq_one]; exact ha2
  have hupper : ∀ t : F, upper t ∈ commutator (SpecialLinearGroup (Fin 2) F) := by
    intro t
    have key : upper t = ⁅diagSL a ha, upper ((a ^ 2 - 1)⁻¹ * t)⁆ := by
      rw [comm_diag_upper a ha]; congr 1
      rw [← mul_assoc, mul_inv_cancel₀ hunit, one_mul]
    rw [key]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hlower : ∀ t : F, lower t ∈ commutator (SpecialLinearGroup (Fin 2) F) := by
    intro t
    have key : lower t = ⁅diagSL a ha, lower ((a⁻¹ ^ 2 - 1)⁻¹ * t)⁆ := by
      rw [comm_diag_lower a ha]; congr 1
      rw [← mul_assoc, mul_inv_cancel₀ hunit', one_mul]
    rw [key]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [eq_top_iff, ← transvections_generate, Subgroup.closure_le]
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact hupper t
  · exact hlower t

/-- Perfectness descends along a surjective group homomorphism. -/
theorem perfect_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (h : commutator G = ⊤) : commutator H = ⊤ := by
  have hmap : commutator H = Subgroup.map f (commutator G) := by
    show ⁅(⊤ : Subgroup H), ⊤⁆ = Subgroup.map f ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [hmap, h, Subgroup.map_top_of_surjective f hf]

/-- **`PSL(2,q)` is perfect** for `q` prime with `4 ≤ q` — the Iwasawa
"perfect" obligation for `PSL_isSimpleGroup` at `n = 2`. -/
theorem PSL2_perfect (q : ℕ) [Fact (Nat.Prime q)] (hq : 4 ≤ q) :
    commutator (PSL 2 q) = ⊤ := by
  have hcard : 4 ≤ Fintype.card (ZMod q) := by rw [ZMod.card]; exact hq
  exact perfect_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (SL2_perfect hcard)

/-! ### Nontriviality of `PSL(2,q)` -/

/-- `upper 1` is not central in `SL(2,F)`: it fails to commute with `lower 1`
(their products differ in the `(0,0)` entry, `1 ≠ 2` in any field). -/
theorem upper_one_notMem_center (F : Type*) [Field F] [DecidableEq F] :
    upper (1 : F) ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [Subgroup.mem_center_iff]
  push_neg
  refine ⟨lower 1, ?_⟩
  intro heq
  have h00 : (lower (1 : F) * upper 1).val 0 0 = (upper (1 : F) * lower 1).val 0 0 := by
    rw [heq]
  simp [upper_val, lower_val] at h00

/-- **`PSL(2,q)` is nontrivial** for every prime `q` — the Iwasawa
`Nontrivial` obligation for `PSL_isSimpleGroup` at `n = 2`. (Holds for all
primes, including the non-simple `q = 2, 3`: `SL(2,q)` is always non-abelian,
so its quotient by the center is nontrivial.) -/
theorem PSL2_nontrivial (q : ℕ) [Fact (Nat.Prime q)] : Nontrivial (PSL 2 q) := by
  unfold PSL Matrix.ProjectiveSpecialLinearGroup
  refine ⟨QuotientGroup.mk' _ (upper (1 : ZMod q)), 1, ?_⟩
  intro hh
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hh
  exact upper_one_notMem_center (ZMod q) hh

/-! ### The center of `SL(2,F)` — kernel of `SL → PSL` -/

/-- **The center of `SL(2,F)` is `{1, -1}`.** A central element commutes with all
transvections, hence is a scalar matrix `c·I` (`mem_range_scalar_iff_commute_…`);
`det = c² = 1` forces `c = ±1`. This pins the kernel `Z` of `SL(2,q) ↠ PSL(2,q)`,
the groundwork for the Iwasawa `FaithfulSMul` obligation (the `ℙ¹` action of
`SL(2,q)` has kernel exactly `Z`, so `PSL(2,q)` acts faithfully). -/
theorem center_SL2 (F : Type*) [Field F] [DecidableEq F]
    (g : SpecialLinearGroup (Fin 2) F) :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff] at hg
    have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 2) F, Commute t.toMatrix g.val := by
      intro t
      have hSL := hg ⟨t.toMatrix, t.det⟩
      have h2 : t.toMatrix * g.val = g.val * t.toMatrix := by
        have := congrArg (fun x : SpecialLinearGroup (Fin 2) F => x.val) hSL
        simpa [SpecialLinearGroup.coe_mul] using this
      exact h2
    rw [← Matrix.mem_range_scalar_iff_commute_transvectionStruct] at hcomm
    obtain ⟨c, hc⟩ := hcomm
    have hval : g.val = !![c, 0; 0, c] := by
      rw [← hc]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    have hdet : c * c = 1 := by
      have h := g.2; rw [hval] at h; simpa [Matrix.det_fin_two_of] using h
    rcases mul_self_eq_one_iff.mp hdet with h1 | h1
    · left; apply Subtype.ext
      rw [hval, h1]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.coe_one, Matrix.one_apply]
    · right; apply Subtype.ext
      rw [hval, h1]; ext i j; fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one, Matrix.one_apply]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Subgroup.mem_center_iff]; intro h; rw [mul_neg_one, neg_one_mul]

/-! ### The action of `SL(2,F)` on the projective line `ℙ¹(F)`

The remaining three Iwasawa obligations (`MulAction`, `IsQuasiPreprimitive`,
`IwasawaStructure`) all need the action of `PSL(2,q)` on `ℙ¹(F_q)`. The
foundation is the linear action of `SL(2,F)` on `Fin 2 → F` by `mulVec`, which
(being linear and commuting with scalars) lifts via mathlib's
`MulAction G (ℙ K V)` instance (`LinearAlgebra/Projectivization/Action.lean`) to
an action on `ℙ¹(F) = Projectivization F (Fin 2 → F)`. The descent to
`PSL = SL/center` (the center `{±1}` fixes every line — `center_SL2`) is the next
step; see `PENDING_WORK §D`. -/

-- The linear `mulVec` action instances of `SL(n,F)` on `n → F` (and the simp
-- lemma `smul_vec_def`, here in scope via `open SLn`) now live once, for general
-- `n`, in `FiniteSimpleGroups.SLnAction`; `Fin 2`-specialised copies here would
-- create instance diamonds at `n = Fin 2`.

/-- **`SL(2,F)` acts on the projective line `ℙ¹(F)`** (via the mathlib
projective-space action instance, fed by the linear `mulVec` action above). The
quotient action of `PSL(2,q)` is obtained by descending through the center
(below). -/
example : MulAction (SpecialLinearGroup (Fin 2) F) (Projectivization F (Fin 2 → F)) :=
  inferInstance

/-! ### Descent to `PSL(2,q)` acting on `ℙ¹(F_q)` — the Iwasawa `MulAction` obligation -/

/-- The projective line `ℙ¹(F_q)`. -/
abbrev P1 (q : ℕ) [Fact (Nat.Prime q)] : Type :=
  Projectivization (ZMod q) (Fin 2 → ZMod q)

/-- The center of `SL(2,q)` acts trivially on `ℙ¹`: the scalars `±1` fix every
line (`−v` and `v` span the same line). -/
theorem center_smul_eq (q : ℕ) [Fact (Nat.Prime q)]
    {z : SpecialLinearGroup (Fin 2) (ZMod q)}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q))) (x : P1 q) :
    z • x = x := by
  rcases (center_SL2 (ZMod q) z).mp hz with rfl | rfl
  · exact one_smul _ x
  · induction x using Projectivization.ind with
    | h v hv =>
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
      refine ⟨-1, ?_⟩
      show (-1 : (ZMod q)ˣ) • v = (-1 : SpecialLinearGroup (Fin 2) (ZMod q)) • v
      rw [smul_vec_def]
      simp [Matrix.neg_mulVec, Units.neg_smul]

/-- The center of `SL(2,q)` lies in the kernel of the permutation action on `ℙ¹`. -/
theorem center_le_ker (q : ℕ) [Fact (Nat.Prime q)] :
    Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q)) ≤
      (MulAction.toPermHom (SpecialLinearGroup (Fin 2) (ZMod q)) (P1 q)).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  ext x
  simpa using center_smul_eq q hz x

/-- **`PSL(2,q)` acts on `ℙ¹(F_q)`** — the Iwasawa `MulAction` obligation,
obtained by descending the `SL(2,q)` action through the center (which acts
trivially, `center_smul_eq`). -/
noncomputable instance psl1Action (q : ℕ) [Fact (Nat.Prime q)] : MulAction (PSL 2 q) (P1 q) :=
  MulAction.compHom (P1 q)
    (QuotientGroup.lift (Subgroup.center _)
      (MulAction.toPermHom (SpecialLinearGroup (Fin 2) (ZMod q)) (P1 q))
      (center_le_ker q))

/-! ### Faithfulness of the `PSL(2,q)` action — the Iwasawa `FaithfulSMul` obligation

The kernel of the `SL(2,q)` action on `ℙ¹` is **exactly** the center (`center_le_ker`
gave `⊇`; the reverse `ker_le_center` is the content here). Hence the descended hom
`PSL(2,q) → Sym(ℙ¹)` is injective, so `PSL(2,q)` acts faithfully. The math core
(`mem_center_of_smul_eq`) is the elementary "an element fixing every line is a
scalar": testing the three lines `[e₁]`, `[e₂]`, `[e₁+e₂]` forces the off-diagonal
entries to vanish and the diagonal entries to agree, so `g = a·I` with `det = a² = 1`,
i.e. `a = ±1`, i.e. `g ∈ {±1} = ` center. -/

/-- If `g` fixes the line `[v]` (for `v ≠ 0`), then `g.mulVec v` is a scalar
multiple of `v` (the geometric meaning of "fixes the line"). -/
theorem parallel_of_fixes (q : ℕ) [Fact (Nat.Prime q)]
    (g : SpecialLinearGroup (Fin 2) (ZMod q))
    (h : ∀ x : P1 q, g • x = x)
    (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    ∃ a : (ZMod q)ˣ, (a : ZMod q) • v = g.val.mulVec v := by
  have hx := h (Projectivization.mk _ v hv)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨a, ?_⟩
  rw [show g.val.mulVec v = g • v from (smul_vec_def g v).symm, ← Units.smul_def]
  exact ha

/-- `![x, y] ≠ 0` when its first entry is nonzero. -/
theorem cons_ne_zero_of_fst {q : ℕ} [Fact (Nat.Prime q)] (x y : ZMod q) (hx : x ≠ 0) :
    (![x, y] : Fin 2 → ZMod q) ≠ 0 := fun h => hx (by have := congrFun h 0; simpa using this)

/-- `![x, y] ≠ 0` when its second entry is nonzero. -/
theorem cons_ne_zero_of_snd {q : ℕ} [Fact (Nat.Prime q)] (x y : ZMod q) (hy : y ≠ 0) :
    (![x, y] : Fin 2 → ZMod q) ≠ 0 := fun h => hy (by have := congrFun h 1; simpa using this)

/-- **An `SL(2,q)` element fixing every line of `ℙ¹` is central** (`= ±1`). The
crux of faithfulness: `ker (SL ↠ Sym ℙ¹) ≤ center`. Tests the three lines
`[e₁], [e₂], [e₁+e₂]`: the first two force `g 1 0 = g 0 1 = 0`, the third forces
`g 0 0 = g 1 1`; with `det = 1` this gives `g 0 0 ² = 1`, so `g = ±1`. -/
theorem mem_center_of_smul_eq (q : ℕ) [Fact (Nat.Prime q)]
    (g : SpecialLinearGroup (Fin 2) (ZMod q))
    (h : ∀ x : P1 q, g • x = x) :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q)) := by
  have h1 : (1 : ZMod q) ≠ 0 := one_ne_zero
  obtain ⟨a0, ha0⟩ := parallel_of_fixes q g h ![1, 0] (cons_ne_zero_of_fst 1 0 h1)
  obtain ⟨a1, ha1⟩ := parallel_of_fixes q g h ![0, 1] (cons_ne_zero_of_snd 0 1 h1)
  obtain ⟨a2, ha2⟩ := parallel_of_fixes q g h ![1, 1] (cons_ne_zero_of_fst 1 1 h1)
  have hc : g.val 1 0 = 0 := by
    have e := congrFun ha0 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, mul_zero, mul_one, add_zero] at e
    exact e.symm
  have hb : g.val 0 1 = 0 := by
    have e := congrFun ha1 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, mul_zero, mul_one, zero_add] at e
    exact e.symm
  have had : g.val 0 0 = g.val 1 1 := by
    have e0 := congrFun ha2 0
    have e1 := congrFun ha2 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, mul_one] at e0 e1
    have key : g.val 0 0 + g.val 0 1 = g.val 1 0 + g.val 1 1 := e0.symm.trans e1
    linear_combination key - hb + hc
  have hdet : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
    have := g.2; rwa [Matrix.det_fin_two] at this
  have hsq : g.val 0 0 * g.val 0 0 = 1 := by
    rw [← had] at hdet; rw [hb, zero_mul, sub_zero] at hdet; exact hdet
  rw [center_SL2]
  rcases mul_self_eq_one_iff.mp hsq with ha | ha
  · left
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp_all [Matrix.one_apply]
  · right
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;>
      simp_all [SpecialLinearGroup.coe_neg, Matrix.one_apply]

/-- **The kernel of the `ℙ¹` action equals the center** — combined with
`center_le_ker`, `ker (toPermHom) = center`. -/
theorem ker_le_center (q : ℕ) [Fact (Nat.Prime q)] :
    (MulAction.toPermHom (SpecialLinearGroup (Fin 2) (ZMod q)) (P1 q)).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q)) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  apply mem_center_of_smul_eq q g
  intro x
  have := (Equiv.ext_iff.mp hg) x
  simpa using this

/-- The descended permutation representation `PSL(2,q) → Sym(ℙ¹)`. The
`psl1Action` instance is `MulAction.compHom` of this hom. -/
noncomputable def pslPermHom (q : ℕ) [Fact (Nat.Prime q)] : PSL 2 q →* Equiv.Perm (P1 q) :=
  QuotientGroup.lift (Subgroup.center _)
    (MulAction.toPermHom (SpecialLinearGroup (Fin 2) (ZMod q)) (P1 q))
    (center_le_ker q)

theorem pslPermHom_mk (q : ℕ) [Fact (Nat.Prime q)]
    (g : SpecialLinearGroup (Fin 2) (ZMod q)) :
    pslPermHom q (QuotientGroup.mk g) =
      MulAction.toPermHom (SpecialLinearGroup (Fin 2) (ZMod q)) (P1 q) g := rfl

/-- `pslPermHom` is injective: its kernel is `ker (toPermHom) / center = ⊥`
because `ker (toPermHom) = center` (`ker_le_center`). -/
theorem pslPermHom_injective (q : ℕ) [Fact (Nat.Prime q)] :
    Function.Injective (pslPermHom q) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [pslPermHom_mk] at hx
    exact (QuotientGroup.eq_one_iff g).mpr (ker_le_center q (MonoidHom.mem_ker.mpr hx))

/-- **`PSL(2,q)` acts faithfully on `ℙ¹(F_q)`** — the Iwasawa `FaithfulSMul`
obligation. Since `g • x = pslPermHom q g x` (the action is `compHom` of
`pslPermHom`) and `Sym(ℙ¹)` acts faithfully, faithfulness reduces to
`pslPermHom`'s injectivity. -/
noncomputable instance pslFaithful (q : ℕ) [Fact (Nat.Prime q)] :
    FaithfulSMul (PSL 2 q) (P1 q) where
  eq_of_smul_eq_smul {g₁ g₂} hsmul := by
    apply pslPermHom_injective q
    ext x
    exact hsmul x

/-! ### Quasi-preprimitivity via 2-transitivity — the Iwasawa `IsQuasiPreprimitive`
obligation

`PSL(2,q)` is **2-transitive** on `ℙ¹(F_q)`: any ordered pair of distinct lines
maps to any other. A 2-transitive action is primitive
(`isPreprimitive_of_is_two_pretransitive`), and primitive ⇒ quasi-preprimitive
(`IsPreprimitive.isQuasiPreprimitive`). The geometric core is that the linear
`SL(2,F)` action carries the reference frame `([e₁],[e₂])` to any pair of distinct
lines `([v],[w])`: distinct lines are linearly independent (`d := det[v|w] ≠ 0`),
so the determinant-1 matrix with columns `v, d⁻¹w` does the job. -/

/-- **Two 2-D vectors with vanishing cross product are parallel.** If
`det[v|w] = v₀w₁ − v₁w₀ = 0` and `v ≠ 0`, then `w = c·v` for some scalar `c`. The
contrapositive (distinct lines ⇒ `det ≠ 0`) underlies 2-transitivity. -/
theorem parallel_of_det_zero {K : Type*} [Field K]
    (v w : Fin 2 → K) (hv : v ≠ 0)
    (hdet : v 0 * w 1 - v 1 * w 0 = 0) :
    ∃ c : K, w = c • v := by
  by_cases h0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i <;> simp_all
    have hw0 : w 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left hv1
    refine ⟨w 1 / v 1, ?_⟩
    funext i; fin_cases i
    · simp [h0, hw0]
    · show w 1 = (w 1 / v 1) • v 1
      rw [smul_eq_mul, div_mul_cancel₀ _ hv1]
  · refine ⟨w 0 / v 0, ?_⟩
    funext i; fin_cases i
    · show w 0 = (w 0 / v 0) • v 0
      rw [smul_eq_mul, div_mul_cancel₀ _ h0]
    · show w 1 = (w 0 / v 0) • v 1
      rw [smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hdet

/-- The reference point `[e₁] = [1 : 0]` of `ℙ¹`. -/
def E1 (q : ℕ) [Fact (Nat.Prime q)] : P1 q :=
  Projectivization.mk (ZMod q) ![1, 0] (cons_ne_zero_of_fst 1 0 one_ne_zero)

/-- The reference point `[e₂] = [0 : 1]` of `ℙ¹`. -/
def E2 (q : ℕ) [Fact (Nat.Prime q)] : P1 q :=
  Projectivization.mk (ZMod q) ![0, 1] (cons_ne_zero_of_snd 0 1 one_ne_zero)

/-- **The `SL(2,q)` action carries the reference frame `([e₁],[e₂])` to any pair
of distinct lines.** The matrix with columns `v` and `d⁻¹w` (`d = det[v|w] ≠ 0`
since `[v] ≠ [w]`) has determinant 1 and sends `e₁ ↦ v`, `e₂ ↦ d⁻¹w ∥ w`. -/
theorem exists_sl2_maps_ref (q : ℕ) [Fact (Nat.Prime q)]
    (v w : Fin 2 → ZMod q) (hv : v ≠ 0) (hw : w ≠ 0)
    (hPQ : Projectivization.mk (ZMod q) v hv ≠ Projectivization.mk (ZMod q) w hw) :
    ∃ g : SpecialLinearGroup (Fin 2) (ZMod q),
      g • E1 q = Projectivization.mk (ZMod q) v hv ∧
      g • E2 q = Projectivization.mk (ZMod q) w hw := by
  set d := v 0 * w 1 - v 1 * w 0 with hd_def
  have hd : d ≠ 0 := by
    intro hd0
    apply hPQ
    obtain ⟨c, hc⟩ := parallel_of_det_zero v w hv (hd_def ▸ hd0)
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hw hc
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), ?_⟩
    rw [Units.smul_def, Units.val_mk0, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hM_det :
      (!![v 0, d⁻¹ * w 0; v 1, d⁻¹ * w 1] : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 := by
    rw [Matrix.det_fin_two_of]; field_simp; rw [hd_def]; ring
  refine ⟨⟨_, hM_det⟩, ?_, ?_⟩
  · rw [E1, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    rw [one_smul]
    funext i; fin_cases i <;>
      simp [smul_vec_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [E2, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 d⁻¹ (inv_ne_zero hd), ?_⟩
    rw [Units.smul_def, Units.val_mk0]
    funext i; fin_cases i <;>
      simp [smul_vec_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- For any two distinct lines `P ≠ Q`, an `SL(2,q)` element maps the reference
frame to `(P, Q)`. -/
theorem exists_sl2_maps_pair (q : ℕ) [Fact (Nat.Prime q)] (P Q : P1 q) (hPQ : P ≠ Q) :
    ∃ g : SpecialLinearGroup (Fin 2) (ZMod q), g • E1 q = P ∧ g • E2 q = Q := by
  obtain ⟨g, h1, h2⟩ := exists_sl2_maps_ref q P.rep Q.rep
    (Projectivization.rep_nonzero P) (Projectivization.rep_nonzero Q)
    (by rw [Projectivization.mk_rep, Projectivization.mk_rep]; exact hPQ)
  rw [Projectivization.mk_rep] at h1 h2
  exact ⟨g, h1, h2⟩

/-- **`SL(2,q)` is 2-transitive on `ℙ¹`** (on points): any distinct pair maps to
any distinct pair, via composition `g₂ ∘ g₁⁻¹` through the reference frame. -/
theorem sl2_two_trans (q : ℕ) [Fact (Nat.Prime q)] (x0 x1 y0 y1 : P1 q)
    (hx : x0 ≠ x1) (hy : y0 ≠ y1) :
    ∃ g : SpecialLinearGroup (Fin 2) (ZMod q), g • x0 = y0 ∧ g • x1 = y1 := by
  obtain ⟨g1, hg1a, hg1b⟩ := exists_sl2_maps_pair q x0 x1 hx
  obtain ⟨g2, hg2a, hg2b⟩ := exists_sl2_maps_pair q y0 y1 hy
  refine ⟨g2 * g1⁻¹, ?_, ?_⟩
  · rw [← hg1a, SemigroupAction.mul_smul, inv_smul_smul, hg2a]
  · rw [← hg1b, SemigroupAction.mul_smul, inv_smul_smul, hg2b]

/-- The `PSL` action of `mk g` agrees with the `SL` action of `g` on `ℙ¹`
(the action factors through the quotient — how `psl1Action` was built). -/
theorem pslPermHom_mk_smul (q : ℕ) [Fact (Nat.Prime q)]
    (g : SpecialLinearGroup (Fin 2) (ZMod q)) (x : P1 q) :
    pslPermHom q (QuotientGroup.mk g) x = g • x := by
  rw [pslPermHom_mk]; rfl

/-- **`PSL(2,q)` is 2-transitive on `ℙ¹`** (on points), inherited from the `SL`
action via the surjection `SL ↠ PSL`. -/
theorem psl_two_trans (q : ℕ) [Fact (Nat.Prime q)] (x0 x1 y0 y1 : P1 q)
    (hx : x0 ≠ x1) (hy : y0 ≠ y1) :
    ∃ g : PSL 2 q, g • x0 = y0 ∧ g • x1 = y1 := by
  obtain ⟨g, h0, h1⟩ := sl2_two_trans q x0 x1 y0 y1 hx hy
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · show pslPermHom q (QuotientGroup.mk g) x0 = y0
    rw [pslPermHom_mk_smul]; exact h0
  · show pslPermHom q (QuotientGroup.mk g) x1 = y1
    rw [pslPermHom_mk_smul]; exact h1

/-- **`PSL(2,q)` is 2-pretransitive on `ℙ¹`** (the mathlib `IsMultiplyPretransitive`
form, on ordered pairs `Fin 2 ↪ ℙ¹`). -/
theorem psl_two_pretrans (q : ℕ) [Fact (Nat.Prime q)] :
    MulAction.IsMultiplyPretransitive (PSL 2 q) (P1 q) 2 := by
  rw [MulAction.isMultiplyPretransitive_iff]
  intro x y
  have hx : x 0 ≠ x 1 := fun h => absurd (x.injective h) (by decide)
  have hy : y 0 ≠ y 1 := fun h => absurd (y.injective h) (by decide)
  obtain ⟨g, hg0, hg1⟩ := psl_two_trans q (x 0) (x 1) (y 0) (y 1) hx hy
  refine ⟨g, ?_⟩
  ext i
  fin_cases i
  · simpa [Function.Embedding.smul_apply] using hg0
  · simpa [Function.Embedding.smul_apply] using hg1

/-- **`PSL(2,q)`'s action on `ℙ¹` is quasi-preprimitive** — the Iwasawa
`IsQuasiPreprimitive` obligation. From 2-transitivity: 2-transitive ⇒ primitive
(`isPreprimitive_of_is_two_pretransitive`) ⇒ quasi-preprimitive. -/
noncomputable instance pslQuasiPreprimitive (q : ℕ) [Fact (Nat.Prime q)] :
    MulAction.IsQuasiPreprimitive (PSL 2 q) (P1 q) :=
  haveI : MulAction.IsPreprimitive (PSL 2 q) (P1 q) :=
    MulAction.isPreprimitive_of_is_two_pretransitive (psl_two_pretrans q)
  inferInstance

/-! ### Transvection subgroups — groundwork for the Iwasawa structure

The last Iwasawa obligation is an `IwasawaStructure (PSL 2 q) ℙ¹`: a
conjugation-equivariant family `T : ℙ¹ → Subgroup (PSL 2 q)` of abelian subgroups
generating the group. We take `T x` = image in PSL of the **transvection subgroup
along the line `x`**: `transvecGroup v = { transSL v c : c ∈ F }`, where
`transSL v c = I + c·(v ⊗ vrot)` (`vrot = (−v₁, v₀)`) is the transvection fixing
`[v]`. The crux is `trans_mul_comm`: conjugation carries `transSL v c` to
`transSL (g·v) c` *exactly* (for `det g = 1`, since `gᵀ⁻¹·vrot = (g·v)rot`), which
makes the family conjugation-equivariant. This section builds that machinery up to
the abelian PSL-level family `Tline`; the `IwasawaStructure` record assembling it
(conjugation-equivariance `Tline_conj`, generation) is in progress — see
`PENDING_WORK §D`. -/

def transMat (v : Fin 2 → F) (c : F) : Matrix (Fin 2) (Fin 2) F :=
  !![1 - c * v 0 * v 1, c * v 0 * v 0; -(c * v 1 * v 1), 1 + c * v 0 * v 1]

theorem trans_mul_comm (g : Matrix (Fin 2) (Fin 2) F) (hg : g.det = 1)
    (v : Fin 2 → F) (c : F) :
    g * transMat v c = transMat (g.mulVec v) c * g := by
  rw [Matrix.det_fin_two] at hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [transMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (c * (g 0 0 * v 0 + g 0 1 * v 1) * v 1) * hg
  · linear_combination (-(c * (g 0 0 * v 0 + g 0 1 * v 1) * v 0)) * hg
  · linear_combination (c * (g 1 0 * v 0 + g 1 1 * v 1) * v 1) * hg
  · linear_combination (-(c * (g 1 0 * v 0 + g 1 1 * v 1) * v 0)) * hg

def transSL (v : Fin 2 → F) (c : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨transMat v c, by simp only [transMat, Matrix.det_fin_two_of]; ring⟩

@[simp] theorem transSL_val (v : Fin 2 → F) (c : F) : (transSL v c).val = transMat v c := rfl

theorem transMat_mul (v : Fin 2 → F) (c c' : F) :
    transMat v c * transMat v c' = transMat v (c + c') := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [transMat, Matrix.mul_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> ring

theorem transSL_mul (v : Fin 2 → F) (c c' : F) :
    transSL v c * transSL v c' = transSL v (c + c') := by
  apply Subtype.ext; simp only [SpecialLinearGroup.coe_mul, transSL_val]; exact transMat_mul v c c'

theorem transSL_zero (v : Fin 2 → F) : transSL v 0 = 1 := by
  apply Subtype.ext
  simp only [transSL_val, transMat, mul_zero, zero_mul, sub_zero, add_zero, neg_zero,
    SpecialLinearGroup.coe_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-- The additive parameter `c ↦ transSL v c` as a monoid hom from `Multiplicative F`. -/
def transHom (v : Fin 2 → F) : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun c := transSL v c.toAdd
  map_one' := transSL_zero v
  map_mul' a b := (transSL_mul v _ _).symm

@[simp] theorem transHom_apply (v : Fin 2 → F) (c : Multiplicative F) :
    transHom v c = transSL v (Multiplicative.toAdd c) := rfl

/-- **The conjugate of a transvection-along-`v` is a transvection-along-`g·v`** (no
rescaling) — the SL-level identity powering Iwasawa conjugation-equivariance. -/
theorem transSL_conj (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (c : F) :
    g * transSL v c * g⁻¹ = transSL (g.val.mulVec v) c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show g.val * (transSL v c).val = (transSL (g.val.mulVec v) c).val * g.val
  simp only [transSL_val]
  exact trans_mul_comm g.val g.2 v c

/-- The transvection subgroup along a line: `{ transSL v c : c ∈ F }`. -/
def transvecGroup (v : Fin 2 → F) : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  (transHom v).range

instance (v : Fin 2 → F) : IsMulCommutative (transvecGroup v) := by
  unfold transvecGroup; infer_instance

theorem mem_transvecGroup {v : Fin 2 → F} {y : SpecialLinearGroup (Fin 2) F} :
    y ∈ transvecGroup v ↔ ∃ c : F, transSL v c = y := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c.toAdd, rfl⟩
  · rintro ⟨c, rfl⟩; exact ⟨Multiplicative.ofAdd c, rfl⟩

/-- Conjugating `transvecGroup v` by `g` gives `transvecGroup (g·v)`. -/
theorem transvecGroup_conj (g : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
    (transvecGroup v).map (MulAut.conj g) = transvecGroup (g.val.mulVec v) := by
  ext y
  simp only [Subgroup.mem_map, mem_transvecGroup]
  constructor
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (transSL_conj g v c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨transSL v c, ⟨c, rfl⟩, transSL_conj g v c⟩

/-- Scaling the line representative by a nonzero `a` doesn't change the transvection
subgroup. -/
theorem transMat_smul (a : F) (v : Fin 2 → F) (c : F) :
    transMat (a • v) c = transMat v (a ^ 2 * c) := by
  simp only [transMat, Pi.smul_apply, smul_eq_mul]; ring_nf

theorem transvecGroup_smul (a : F) (ha : a ≠ 0) (v : Fin 2 → F) :
    transvecGroup (a • v) = transvecGroup v := by
  apply le_antisymm <;> rw [SetLike.le_def] <;> intro y hy <;>
    rw [mem_transvecGroup] at hy ⊢ <;> obtain ⟨c, rfl⟩ := hy
  · exact ⟨a ^ 2 * c, by apply Subtype.ext; rw [transSL_val, transSL_val, transMat_smul]⟩
  · refine ⟨(a ^ 2)⁻¹ * c, ?_⟩
    apply Subtype.ext
    rw [transSL_val, transSL_val, transMat_smul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ha),
      one_mul]

/-! ### PSL-level transvection subgroups and the Iwasawa structure -/

/-- `Tline x` = image in `PSL(2,q)` of the transvection subgroup along the line `x`
(using the chosen representative `x.rep`). -/
noncomputable def Tline (q : ℕ) [Fact (Nat.Prime q)] (x : P1 q) : Subgroup (PSL 2 q) :=
  (transvecGroup x.rep).map (QuotientGroup.mk' (Subgroup.center _))

instance (q : ℕ) [Fact (Nat.Prime q)] (x : P1 q) : IsMulCommutative (Tline q x) := by
  unfold Tline; infer_instance



/-! ### The Iwasawa structure and simplicity of `PSL(2,q)`

Assembling the four `IwasawaStructure` fields — `Tline` (the family of abelian
transvection subgroups), conjugation-equivariance (`Tline_conj`), and generation
(`Tline_iSup`) — discharges the final Iwasawa obligation. With the five obligations
proved above, `PSL2_isSimpleGroup_of_iwasawa` then yields **`PSL(2,q)` simple for
every prime `q ≥ 4`** (`PSL2_isSimpleGroup`), `#print axioms`-clean. This discharges
`PSL_isSimpleGroup` (the deep CFSG `axiom` in `LieType`) at `n = 2`. -/

/-- **Conjugation-equivariance of `Tline`** — the Iwasawa `is_conj` obligation:
`T (g • x) = MulAut.conj g • T x`, from `transvecGroup_conj` (conjugating a
transvection along `v` yields one along `g·v`) pushed through the quotient. -/
theorem Tline_conj (q : ℕ) [Fact (Nat.Prime q)] (g : PSL 2 q) (x : P1 q) :
    Tline q (g • x) = MulAut.conj g • Tline q x := by
  obtain ⟨g_SL, hg⟩ := QuotientGroup.mk_surjective g
  have hne : g_SL.val.mulVec x.rep ≠ 0 := by
    rw [← smul_vec_def]; exact (smul_ne_zero_iff_ne g_SL).mpr (Projectivization.rep_nonzero x)
  have hgx : g • x = Projectivization.mk (ZMod q) (g_SL.val.mulVec x.rep) hne := by
    rw [← hg]
    show g_SL • x = Projectivization.mk (ZMod q) (g_SL.val.mulVec x.rep) hne
    conv_lhs => rw [← Projectivization.mk_rep x]
    rw [Projectivization.smul_mk]
    rfl
  have hpar : transvecGroup ((g • x).rep) = transvecGroup (g_SL.val.mulVec x.rep) := by
    have h2 : Projectivization.mk (ZMod q) ((g • x).rep) (Projectivization.rep_nonzero _)
        = Projectivization.mk (ZMod q) (g_SL.val.mulVec x.rep) hne := by
      rw [Projectivization.mk_rep]; exact hgx
    rw [Projectivization.mk_eq_mk_iff] at h2
    obtain ⟨a, ha⟩ := h2
    rw [← ha, Units.smul_def]
    exact transvecGroup_smul _ (Units.ne_zero a) _
  rw [show (MulAut.conj g) • Tline q x = (Tline q x).map (MulAut.conj g) from
        Subgroup.toSubmonoid_inj.mp rfl]
  rw [Tline, Tline, hpar, ← transvecGroup_conj g_SL]
  simp only [Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun z => ?_
  change (QuotientGroup.mk' (Subgroup.center _)) (g_SL * z * g_SL⁻¹)
      = MulAut.conj g ((QuotientGroup.mk' (Subgroup.center _)) z)
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ← hg]
  rfl

/-- `transvecGroup` of a representative of `[v]` equals that of `v` (line-invariance). -/
theorem transvecGroup_rep (q : ℕ) [Fact (Nat.Prime q)] (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    transvecGroup ((Projectivization.mk (ZMod q) v hv).rep) = transvecGroup v := by
  have h2 : Projectivization.mk (ZMod q) ((Projectivization.mk (ZMod q) v hv).rep)
        (Projectivization.rep_nonzero _) = Projectivization.mk (ZMod q) v hv := by
    rw [Projectivization.mk_rep]
  rw [Projectivization.mk_eq_mk_iff] at h2
  obtain ⟨a, ha⟩ := h2
  rw [← ha, Units.smul_def]
  exact transvecGroup_smul _ (Units.ne_zero a) _

theorem Tline_mk (q : ℕ) [Fact (Nat.Prime q)] (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    Tline q (Projectivization.mk (ZMod q) v hv) = (transvecGroup v).map (QuotientGroup.mk' _) :=
  congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center _))) (transvecGroup_rep q v hv)

theorem transSL_e1 (c : F) : transSL (![1, 0] : Fin 2 → F) c = upper c := by
  apply Subtype.ext
  simp only [transSL_val, upper_val, transMat]
  norm_num

theorem transSL_e2 (c : F) : transSL (![0, 1] : Fin 2 → F) c = lower (-c) := by
  apply Subtype.ext
  simp only [transSL_val, lower_val, transMat]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num


theorem Tline_iSup (q : ℕ) [Fact (Nat.Prime q)] : iSup (Tline q) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨y_SL, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) y
  -- every generator `mk'(upper c)`, `mk'(lower c)` lies in some `Tline`, so `S` lies
  -- in the preimage of `iSup Tline`; `S` generates SL, so the preimage is `⊤`.
  have hsub : S (F := ZMod q) ⊆ ((iSup (Tline q)).comap (QuotientGroup.mk' _) : Subgroup _) := by
    rintro w (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine Subgroup.mem_comap.mpr (le_iSup (Tline q) (E1 q) ?_)
      rw [E1, Tline_mk]
      exact Subgroup.mem_map_of_mem _ (mem_transvecGroup.mpr ⟨c, transSL_e1 c⟩)
    · refine Subgroup.mem_comap.mpr (le_iSup (Tline q) (E2 q) ?_)
      rw [E2, Tline_mk]
      exact Subgroup.mem_map_of_mem _ (mem_transvecGroup.mpr ⟨-c, by rw [transSL_e2, neg_neg]⟩)
  have hmem : y_SL ∈ (iSup (Tline q)).comap (QuotientGroup.mk' _) := by
    have h := (Subgroup.closure_le _).mpr hsub
    rw [transvections_generate] at h
    exact h (Subgroup.mem_top y_SL)
  exact Subgroup.mem_comap.mp hmem


/-- **The Iwasawa structure on `PSL(2,q) ↷ ℙ¹`.** -/
noncomputable def pslIwasawa (q : ℕ) [Fact (Nat.Prime q)] :
    MulAction.IwasawaStructure (PSL 2 q) (P1 q) where
  T := Tline q
  is_comm := fun x => inferInstance
  is_conj := Tline_conj q
  is_generator := Tline_iSup q

/-- **`PSL(2,q)` is simple for every prime `q ≥ 4`** — the Iwasawa criterion
applied to the action on `ℙ¹(F_q)`, with all six obligations machine-checked.
This discharges `PSL_isSimpleGroup` at `n = 2` (for prime `q ≥ 4`). -/
theorem PSL2_isSimpleGroup (q : ℕ) [Fact (Nat.Prime q)] (hq : 4 ≤ q) :
    IsSimpleGroup (PSL 2 q) :=
  haveI : Nontrivial (PSL 2 q) := PSL2_nontrivial q
  PSL2_isSimpleGroup_of_iwasawa q (PSL2_perfect q hq) (pslIwasawa q) (pslFaithful q)

/-! ### The order of `PSL(2,q)`

With `card_SL2` (`|SL(2,q)| = q(q²−1)`) and `center_SL2` (the center is `{±1}`),
Lagrange pins `|PSL(2,q)| = q(q²−1)/2` for odd prime `q`. This is the order-pin
companion to the simplicity thread — the `Nat.card`-as-function-of-`(fam,n,q)`
faithfulness anchor flagged as the natural next step in `Classification.lean`. -/

/-- **`|Z(SL(2,𝔽_q))| = 2`** for odd prime `q`. The center is `{1, -1}`
(`center_SL2`); the two are distinct because `1 = -1` would force `2 = 0` in
`ZMod q`, impossible for odd `q`. -/
theorem card_center_SL2 (q : ℕ) [Fact (Nat.Prime q)] (hodd : Odd q) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q))) = 2 := by
  have hq : Nat.Prime q := Fact.out
  have hne : (1 : SpecialLinearGroup (Fin 2) (ZMod q)) ≠ -1 := by
    intro h
    have hval : (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) = -1 := by
      have := congrArg Subtype.val h
      simpa [SpecialLinearGroup.coe_one, SpecialLinearGroup.coe_neg] using this
    have h2 : (1 : ZMod q) = -1 := by
      have := congrFun (congrFun hval 0) 0
      simpa [Matrix.one_apply] using this
    have hz : ((2 : ℕ) : ZMod q) = 0 := by
      have h11 : (1 : ZMod q) + 1 = 0 := by linear_combination h2
      push_cast; linear_combination h11
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd
    rw [this] at hodd
    exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
  have hset : (↑(Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q))) :
      Set (SpecialLinearGroup (Fin 2) (ZMod q))) = {1, -1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact center_SL2 (ZMod q) g
  have e : ↥(Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q))) ≃
      ↥({1, -1} : Set (SpecialLinearGroup (Fin 2) (ZMod q))) := Equiv.setCongr hset
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- **`|PSL(2,q)| · 2 = q(q²−1)`** for odd prime `q` — equivalently
`|PSL(2,q)| = q(q²−1)/2`. Lagrange applied to `SL(2,q) ↠ PSL(2,q)` with kernel
the order-2 center (`card_center_SL2`), and `card_SL2`. -/
theorem card_PSL2 (q : ℕ) [Fact (Nat.Prime q)] (hodd : Odd q) :
    Nat.card (PSL 2 q) * 2 = q * (q ^ 2 - 1) := by
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) (ZMod q)) = q * (q ^ 2 - 1) :=
    Nat.card_eq_fintype_card.trans (card_SL2 q)
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod q)))
  rw [card_center_SL2 q hodd, hSL] at hlag
  exact hlag.symm


end SL2

/-- **`PSL(n, 𝔽_p)` is simple** for every prime `q = p`, dimension `n ≥ 2`, outside
the two genuinely non-simple small cases `PSL(2,2) ≅ S₃` and `PSL(2,3) ≅ A₄`
(captured by `h_skip : ¬ (n = 2 ∧ q ≤ 3)`).

This is the unified discharge of the former monolithic `axiom PSL_isSimpleGroup`
(which was unsound for composite `q`; see `LieType.lean`). The two cases:

* `n = 2`: fully machine-checked — `SL2.PSL2_isSimpleGroup` (Iwasawa criterion on
  the `PSL(2,q) ↷ ℙ¹(𝔽_q)` action, all six obligations proved in `SL2.lean`).
  Here `h_skip` forces `4 ≤ q`.
* `n ≥ 3`: the genuinely-deep classical result `PSL_isSimpleGroup_rank_ge_three`
  (Dickson/Dieudonné), the sole remaining axiom.

So `#print axioms PSL_isSimpleGroup` = `[PSL_isSimpleGroup_rank_ge_three, propext,
Classical.choice, Quot.sound]` — the `n = 2` case contributes no extra debt. -/
theorem PSL_isSimpleGroup (n q : ℕ) [Fact (Nat.Prime q)]
    (h_n : 2 ≤ n) (h_skip : ¬ (n = 2 ∧ q ≤ 3)) :
    IsSimpleGroup (PSL n q) := by
  rcases lt_or_ge n 3 with h2 | h3
  · -- `2 ≤ n < 3`, so `n = 2`; then `h_skip` forces `4 ≤ q`.
    have hn2 : n = 2 := by omega
    subst hn2
    have hq3 : ¬ q ≤ 3 := fun h => h_skip ⟨rfl, h⟩
    exact SL2.PSL2_isSimpleGroup q (by omega)
  · -- `n ≥ 3`: discharged via the Iwasawa criterion on `ℙ^{n-1}` (`SLnIwasawa`), modulo the
    -- two disclosed geometric axioms (transvections generate `SLₙ`; `SLₙ` 2-transitive on `ℙ`).
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have hcard : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact h3
    exact SLn.PSLn_isSimpleGroup_of_rank (n := Fin n) (F := ZMod q) hcard

end FiniteSimpleGroups

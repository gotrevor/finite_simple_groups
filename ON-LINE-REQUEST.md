# Online research requests (box has no general web; a networked session fulfills these)

Fulfiller protocol: answer in a committed `ON-LINE-FINDINGS-<date>-<topic>.md`, DELETE the answered
item below, and remove this file once nothing is left open.

---

## 2026-06-04 — Witt's extension theorem for Hermitian forms (the PSU wall)

**Context.** The PSU(n,q) simplicity formalization (`FiniteSimpleGroups/UnitarySimple.lean`) is now
fully reduced: `PSU_isSimpleGroup_of_generate_of_eichler'` derives `IsSimpleGroup (PSUConcrete n p)`
(n≥3, p≥5) from exactly four geometric atoms — `hgen` (transvections generate SU), `hT1`/`hT2`
(stabilizer transitivity on non-perp / perp isotropic points), and `hPP` (∃ isotropic `v` with
`⟨x,v⟩=1, ⟨y,v⟩=0`). For **n=3** only `{hgen, hT1}` are needed (perp atoms vacuous). Everything
*around* these atoms is machine-checked (axiom-clean). An Aristotle auto-formalization run on `hgen`
returned that the core "requires Witt's extension theorem for Hermitian forms, not available in
Mathlib." All four atoms reduce to the same building block: **"in a nondegenerate Hermitian space of
dimension ≥ 2 over `F_{q²}`, every nonzero isotropic vector has a hyperbolic partner"** (and its
relative/subspace form), i.e. Witt's theorem.

**UPDATE 2026-06-04 (latest):** `hPP`, `hT2`, AND now **`hT1`** are ALL DISCHARGED locally without
Witt. `hT1` fell to an **explicit Eichler/Siegel transformation matrix** `E = 1 + h⊗x̄ − x⊗h̄ − μ·x⊗x̄`
(`uEichler`, `UnitaryTransvection.lean`): a rank-≤2 update, `star E·E=1` by direct expansion, `det E=1`
by Weinstein–Aronszajn, and the correction transvection's scalar is automatically trace-zero because
the points are isotropic. **PSU(n,p²) simplicity (n≥3, p≥5) now needs the SINGLE atom `hgen`**
(`PSU_isSimpleGroup_modulo_generation`, axiom-clean). The remaining wall is purely **`hgen`** —
unitary transvections generate `SU_n(F_{q²})`, n≥3. **Only item 3 below is live** (a direct /
finite-field proof of unitary transvection generation, or an existing Lean formalization to port).
Items 1 (general Witt/orthogonal-complement search — still useful for the dimension induction in
`hgen`), 2 (point counts), and all Eichler/separation asks are MOOT or subsumed.

**The `hgen` ask, sharpened:** the standard proof is the Dieudonné/Eichler **dimension induction**:
a `g∈SU` fixing a hyperbolic pair `(e,f)` pointwise restricts to `SU` on the orthogonal complement
`⟨e,f⟩^⊥` (a nondegenerate Hermitian space of dim n−2), where transvections generate by induction
and lift back (centred in `⟨e,f⟩^⊥`, so they fix `e,f`). The SAME gap blocks the symplectic
`sp_stab_hyperbolic_le`. **What would unblock fastest:** (i) any mathlib/Lean machinery for the
orthogonal complement of a hyperbolic plane under a NONdegenerate sesquilinear form and its
`finrank = n−2` (so I can set up the induction); (ii) a clean textbook statement of the
reduction-to-pair-stabilizer step (Grove §6, Taylor Ch. 8/11) I can port move-by-move.

**What I need (any subset helps, in priority order):**

1. **Existing Lean/mathlib formalization.** Does mathlib4 (or any public Lean project — search
   Reservoir, GitHub `leanprover-community`, Mathlib `LinearAlgebra/SesquilinearForm`,
   `QuadraticForm/`, `BilinearForm/`) contain ANY of: Witt's extension/cancellation theorem; the
   orthogonal-complement decomposition `V = H ⊕ Hᗮ` for a nondegenerate **sesquilinear/Hermitian**
   form; "isotropic vector ⇒ hyperbolic plane" for Hermitian forms; `finrank` of the orthogonal
   complement for a NONdegenerate sesquilinear (not just bilinear) form? Mathlib has
   `LinearMap.BilinForm.orthogonal` + `finrank_orthogonal` for **bilinear** forms — is there a
   sesquilinear analogue, or a clean way to apply the bilinear machinery to a conjugate-linear
   Hermitian form (e.g. via restriction of scalars to the fixed field `F_p`)? Exact declaration
   names + file paths, please.

2. **Cleanest textbook proof for the FINITE-FIELD case.** For `F = F_{q²}` with `q`-Frobenius
   involution, I only need the finite-field instance. Two candidate routes — which is shorter to
   formalize, and what's the cleanest reference?
   - (a) Witt's theorem proper (Grove, *Classical Groups and Geometric Algebra*; Taylor, *The
     Geometry of the Classical Groups*; Dieudonné). Statement + the induction that gives the
     hyperbolic-partner-in-subspace lemma.
   - (b) **Point-counting**: the number of isotropic points of a nondegenerate Hermitian form, and
     of an affine slice `{v : ⟨x,v⟩=1, ⟨y,v⟩=0}` of dimension n-2. I want a clean formula (or a lower
     bound > 0) for the count of `v` with `⟨v,v⟩=0` in such an affine subspace, for n ≥ 3/4. Is there
     a Chevalley–Warning-style argument (the norm form `Σ vᵢ^{q+1}` has degree q+1, so CW needs many
     variables — does Warning's *second* theorem or a Hermitian-specific count rescue small n)?
     References for Hermitian variety point counts over `F_{q²}` (e.g. Hirschfeld, *Projective
     Geometries over Finite Fields*).

3. **Generation of SU by transvections — finite-field shortcut.** Any reference giving a *direct*
   (non-Witt) proof that the unitary transvections generate `SU_n(F_{q²})` for n ≥ 3 (Dickson;
   Dieudonné; or the "Eichler transformation" generation argument). A self-contained induction we
   could port would let us discharge `hgen` without the full Witt machinery.

**Why it unblocks:** any of these collapses all four PSU atoms (they share the wall). #1 (an existing
formalization to port) is the biggest win; #2b (finite-field counting) is the most self-contained
new build; #3 handles `hgen` specifically (which closes PSU(3) together with the in-flight `t1`).

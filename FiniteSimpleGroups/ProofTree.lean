import FiniteSimpleGroups.ProofStrategy

/-!
# The CFSG proof tree — layers 3–4 (documented GUESSES) 🌳

`ProofStrategy.lean` states the **depth-2** skeleton of the second-generation
(Gorenstein–Lyons–Solomon) proof: the odd/even split, the component-vs-
characteristic-2 dichotomy, and the quasithin cut. Those milestones
(`componentType_isClassified`, `nonQuasithin_char2_isClassified`, …) are honest
leaf `axiom`s there.

This file pushes the two *generic* branches **two layers deeper**, so the tree
shows where each branch actually heads. **Everything here is a documented GUESS**
— the predicates are `opaque` placeholders and the implications are `axiom`s whose
statements approximate the real theorems but have NOT been checked against
Gorenstein–Lyons–Solomon Vol 1–2. They are scaffolding for *understanding the
architecture*, not faithful formalizations. Each is tagged `GUESS:` with the real
theorem it gestures at. The point (per the learning-scaffold charter): a labeled,
navigable map you can correct beats no map.

What is NOT deepened, and why:
* **odd branch** — already a real theorem (`feitThompson_dichotomy`); its depth
  lives in the `FeitThompson/` B&G §1 port.
* **quasithin branch** — Aschbacher–Smith is a ~1200-page monolith; it stays a
  single cited leaf, not decomposed.

The capstone `classification_via_deep_tree` reassembles CFSG threading the two
deepened branches, so `#print axioms` on it exhibits the deeper guessed leaves
(`B_theorem`, `trichotomy_theorem`, `bnPair_isClassified`, …) in place of the two
collapsed milestones.
-/

namespace FiniteSimpleGroups

/-! ## Component-type branch (depth 3–4)

`C_G(t)` has a component (a quasisimple subnormal piece, modulo its core). The
program: tame the core (B-theorem), put `G` in *standard form* relative to the
known component, then *identify* it. Heads to `A_n`, Lie type in **odd**
characteristic, and most sporadics. -/

/-- GUESS (depth-3 vocabulary): the core `O(C_G(t))` of an involution centralizer
is tame, so the component is visible in `C_G(t)` itself. -/
opaque HasTameCore (G : Type*) [Group G] : Prop

/-- GUESS (depth-3 vocabulary): `G` is in *standard form* with respect to a known
quasisimple component `L` — i.e. `C_G(t)` is essentially `L` extended in a
controlled way, the configuration from which `G` can be recognized. -/
opaque IsStandardForm (G : Type*) [Group G] : Prop

/-- **B-theorem** (formerly the B-conjecture). GUESS: in a component-type simple
group, the core of every involution centralizer is tame, exposing the components.
Proved across the program (Aschbacher, Gilman–Griess, …); shape only, unchecked. -/
axiom B_theorem (G : Type*) [Group G] [IsFSG G]
    (h : IsComponentType G) : HasTameCore G

/-- **Standard-form reduction.** GUESS: component-type + tame core ⟹ `G` sits in
standard form relative to its component (Aschbacher's Classical Involution Theorem
and the family of standard-form problems). Shape only, unchecked. -/
axiom componentType_standardForm (G : Type*) [Group G] [IsFSG G]
    (h : IsComponentType G) (ht : HasTameCore G) : IsStandardForm G

/-- **Identification of standard-form groups.** GUESS: a simple group in standard
form is one of `A_n`, an odd-characteristic Lie type, or a sporadic — i.e. it is
classified. This is the depth-4 leaf where per-family recognition lives. -/
axiom standardForm_isClassified (G : Type*) [Group G] [IsFSG G]
    (h : IsStandardForm G) : IsClassified G

/-- **Depth-4 assembly of the component-type milestone.** Derives
`IsComponentType G → IsClassified G` from the three guessed sub-interfaces above,
in place of the single `componentType_isClassified` axiom. -/
theorem componentType_isClassified_via_tree (G : Type*) [Group G] [IsFSG G]
    (h : IsComponentType G) : IsClassified G :=
  standardForm_isClassified G (componentType_standardForm G h (B_theorem G h))

/-! ## Generic even / characteristic-2 branch (depth 3–4)

2-local subgroups look like those of a Lie-type group in characteristic 2. For
2-local rank `e(G) ≥ 3` (the non-quasithin, generic case): run Aschbacher's
Trichotomy Theorem to reach *standard type*, extract a BN-pair / building, and
identify `G` as Lie type in characteristic 2 (Tits, Curtis–Tits, Gilman–Griess). -/

/-- GUESS (depth-3 vocabulary): `G` is of *standard type* — the favorable output
of the Trichotomy Theorem, from which a BN-pair can be constructed. -/
opaque IsStandardType (G : Type*) [Group G] : Prop

/-- GUESS (depth-3 vocabulary): `G` admits a (thick, spherical, rank `≥ 3`)
BN-pair, equivalently acts suitably on a building. -/
opaque HasBNPair (G : Type*) [Group G] : Prop

/-- **Trichotomy Theorem** (Aschbacher, `e(G) ≥ 3`). GUESS: a non-quasithin
characteristic-2-type simple group is of standard type (collapsing the uniqueness
and exceptional sub-cases of the actual trichotomy). Shape only, unchecked. -/
axiom trichotomy_theorem (G : Type*) [Group G] [IsFSG G]
    (h : IsCharacteristic2Type G) (hq : ¬ IsQuasithin G) : IsStandardType G

/-- **Amalgam / Curtis–Tits–Gilman–Griess step.** GUESS: standard type yields a
BN-pair (build the building from the standard configuration). Shape only. -/
axiom standardType_hasBNPair (G : Type*) [Group G] [IsFSG G]
    (h : IsStandardType G) : HasBNPair G

/-- **BN-pair identification** (Tits). GUESS: a thick spherical BN-pair of rank
`≥ 3` forces `G` to be a group of Lie type — hence classified. The depth-4 leaf
where Tits's classification of buildings does the recognizing. -/
axiom bnPair_isClassified (G : Type*) [Group G] [IsFSG G]
    (h : HasBNPair G) : IsClassified G

/-- **Depth-4 assembly of the generic even milestone.** Derives
`IsCharacteristic2Type G → ¬IsQuasithin G → IsClassified G` from the guessed
trichotomy → BN-pair → identification chain, in place of the single
`nonQuasithin_char2_isClassified` axiom. -/
theorem nonQuasithin_char2_isClassified_via_tree (G : Type*) [Group G] [IsFSG G]
    (h : IsCharacteristic2Type G) (hq : ¬ IsQuasithin G) : IsClassified G :=
  bnPair_isClassified G (standardType_hasBNPair G (trichotomy_theorem G h hq))

/-! ## Capstone: CFSG threaded through the deepened tree -/

/-- **CFSG via the depth-4 tree.** Same conclusion as `CFSG`, but the two generic
branches are routed through the guessed layer-3/4 interfaces instead of their
collapsed milestone axioms. `#print axioms classification_via_deep_tree` therefore
itemizes the deeper structure: `B_theorem`, `standardForm_isClassified`,
`trichotomy_theorem`, `standardType_hasBNPair`, `bnPair_isClassified` — alongside
the still-collapsed `oddType` and `quasithin` leaves. -/
theorem classification_via_deep_tree (G : Type*) [Group G] [IsFSG G] :
    IsClassified G := by
  rcases feitThompson_dichotomy G with hcyc | hinv
  · exact .cyclic hcyc
  · rcases aschbacher_dichotomy G hinv with hodd | heven
    · exact oddType_isClassified G hodd
    · rcases evenType_dichotomy G heven with hcomp | hchar2
      · exact componentType_isClassified_via_tree G hcomp
      · by_cases hqt : IsQuasithin G
        · exact quasithin_isClassified G hchar2 hqt
        · exact nonQuasithin_char2_isClassified_via_tree G hchar2 hqt

end FiniteSimpleGroups

import FiniteSimpleGroups.Basic
import FiniteSimpleGroups.Burnside
import FiniteSimpleGroups.CharacterTheory
import FiniteSimpleGroups.Classification
import FiniteSimpleGroups.Cyclic
import FiniteSimpleGroups.Alternating
import FiniteSimpleGroups.LieType
import FiniteSimpleGroups.Exceptional
import FiniteSimpleGroups.Sporadics
import FiniteSimpleGroups.ProofStrategy
import FiniteSimpleGroups.ProofTree
import FiniteSimpleGroups.SmallOrders
import FiniteSimpleGroups.ClassifiedSmallOrders
import FiniteSimpleGroups.Adjacent.PrimeMul
import FiniteSimpleGroups.FittingSubgroup
import FiniteSimpleGroups.PSLIwasawa
import FiniteSimpleGroups.SLnAction
import FiniteSimpleGroups.SL2
import FiniteSimpleGroups.SLnPerfect
import FiniteSimpleGroups.SLnSimple
import FiniteSimpleGroups.SLnIwasawa
import FiniteSimpleGroups.SpTransvection
import FiniteSimpleGroups.SpAction
import FiniteSimpleGroups.SpSimple
import FiniteSimpleGroups.SpIwasawa
import FiniteSimpleGroups.SpLieType
import FiniteSimpleGroups.SpSmallField
import FiniteSimpleGroups.UnitaryFoundation
import FiniteSimpleGroups.Wielandt
import FiniteSimpleGroups.AschbacherDichotomy
import FiniteSimpleGroups.ComponentCommute

/-!
# Finite Simple Groups — scaffold

This is a *learning scaffold*, not a serious formalization attempt. It states
the shape of the Classification of Finite Simple Groups (CFSG) and the four
infinite families plus 26 sporadic groups.

Most lemmas are `sorry`. The README explains what is and isn't reachable.

The root module re-exports the cluster so `import FiniteSimpleGroups` pulls
everything in.
-/

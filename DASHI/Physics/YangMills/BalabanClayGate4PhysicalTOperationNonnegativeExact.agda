module DASHI.Physics.YangMills.BalabanClayGate4PhysicalTOperationNonnegativeExact where

------------------------------------------------------------------------
-- PHYSICAL T-OPERATION AT 1 IS NONNEGATIVE
--
-- RelativeTPointwiseMeaning already identifies the literal one-integrand with
-- the physical Wilson traversal activity, and its physical carrier owns
-- activityNonnegative.  Therefore the selected finite integrand and its finite
-- constrained fold are nonnegative without identifying the physical density
-- with the stronger Gate4 reference majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Factors
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative

physicalOneIntegrandNonnegative :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : Relative.RelativeSixFactorComparison Scale Traversal}
    (meaning : Relative.RelativeTPointwiseMeaning tData comparison)
    scale component slow fine →
  T.LessEqual (Relative.order meaning)
    (Integral.zero (T.sumData tData))
    (T.localIntegrand tData scale component slow
      (T.oneFunctional tData) fine)
physicalOneIntegrandNonnegative
  {comparison = comparison} meaning scale component slow fine =
  subst
    (λ value →
      T.LessEqual (Relative.order meaning)
        (Integral.zero (T.sumData _))
        value)
    (sym (Relative.oneIntegrandMeaning meaning scale component slow fine))
    (Relative.rationalOrderImpliesTOperationOrder meaning
      (Factors.activityNonnegative
        (Relative.physical comparison)
        scale
        (Relative.traversalOf meaning scale component slow fine)))

selectedPhysicalOneIntegrandNonnegative :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : Relative.RelativeSixFactorComparison Scale Traversal}
    (meaning : Relative.RelativeTPointwiseMeaning tData comparison)
    scale component slow fine →
  T.LessEqual (Relative.order meaning)
    (Integral.zero (T.sumData tData))
    (Integral.selectedWith (T.sumData tData)
      (T.localIntegrand tData scale component slow
        (T.oneFunctional tData))
      slow fine)
selectedPhysicalOneIntegrandNonnegative
  {tData = tData} meaning scale component slow fine
  with Integral.coarseMatches (T.sumData tData) fine slow
... | false =
  T.reflexive (Relative.order meaning)
    (Integral.zero (T.sumData tData))
... | true =
  physicalOneIntegrandNonnegative meaning scale component slow fine

physicalTOperationAtOneNonnegative :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {tData : T.FiniteLocalTOperationData
      Scale Fine SlowField Component Functional ℚ}
    {comparison : Relative.RelativeSixFactorComparison Scale Traversal}
    (meaning : Relative.RelativeTPointwiseMeaning tData comparison)
    scale
    (selected : T.SecondClassComponent (T.classData tData) scale)
    slow →
  T.LessEqual (Relative.order meaning)
    (Integral.zero (T.sumData tData))
    (T.localizedTOperation tData scale selected slow
      (T.oneFunctional tData))
physicalTOperationAtOneNonnegative
  {tData = tData} meaning scale selected slow =
  T.foldNonnegative
    (T.sumData tData)
    (T.LessEqual (Relative.order meaning))
    (T.reflexive (Relative.order meaning))
    (T.addNonnegative (Relative.order meaning))
    (T.fastFibre tData scale (T.component selected))
    (Integral.selectedWith (T.sumData tData)
      (T.localIntegrand tData scale (T.component selected) slow
        (T.oneFunctional tData))
      slow)
    slow
    (selectedPhysicalOneIntegrandNonnegative
      meaning scale (T.component selected) slow)

physicalTOperationAtOneNonnegativeLevel : ProofLevel
physicalTOperationAtOneNonnegativeLevel = machineChecked

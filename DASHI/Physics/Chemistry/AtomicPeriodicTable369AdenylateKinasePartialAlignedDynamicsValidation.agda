module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialAlignedDynamicsValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialAlignedDynamicsExact as P

alignedDynamicsRegression :
  P.AdKPartialAlignedDynamicsBoundary.dependentStateRequiresPaidGraphFigureAlignment
    P.canonicalAdKPartialAlignedDynamicsBoundary
  ≡ true
  × P.AdKPartialAlignedDynamicsBoundary.primaryAlignedPrefixExecutable
    P.canonicalAdKPartialAlignedDynamicsBoundary
  ≡ true
  × P.AdKPartialAlignedDynamicsBoundary.alternativeAlignedPrefixExecutable
    P.canonicalAdKPartialAlignedDynamicsBoundary
  ≡ true
alignedDynamicsRegression = refl , refl , refl

partialityRegression :
  P.AdKPartialAlignedDynamicsBoundary.deltaXiAlignedTransitionAdmitted
    P.canonicalAdKPartialAlignedDynamicsBoundary
  ≡ false
  × P.AdKPartialAlignedDynamicsBoundary.epsilonXiAlignedTransitionAdmitted
    P.canonicalAdKPartialAlignedDynamicsBoundary
  ≡ false
  × P.AdKPartialAlignedDynamicsBoundary.partialDynamicsEqualsCompleteKineticModel
    P.canonicalAdKPartialAlignedDynamicsBoundary
  ≡ false
partialityRegression = refl , refl , refl

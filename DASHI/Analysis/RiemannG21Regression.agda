module DASHI.Analysis.RiemannG21Regression where

import DASHI.Analysis.PoleQuotientedExteriorDeskTestExact as Exterior
import DASHI.Analysis.RiemannG21PrimePairKernelExact as Pair
import DASHI.Analysis.RiemannG21TwoByTwoMixedObstructionExact as Mixed2
import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Det3
import DASHI.Analysis.RiemannG21PoleQuotientedExteriorExact as G21
import DASHI.Analysis.RiemannG21CrossPollinationExact as Cross

open import DASHI.Core.Prelude

regressionDimension :
  Exterior.residualDimension
    Exterior.canonicalExteriorQuotientDimensionReceipt
  ≡ 2
regressionDimension = G21.threeMinusOneLeavesTwo

regressionTwoByTwoNoGo :
  Mixed2.det2Code Mixed2.responseLeft Mixed2.responseRight
  ≡ Mixed2.det2Code Mixed2.commonPole Mixed2.commonPole
  → ⊥
regressionTwoByTwoNoGo = G21.naiveTwoByTwoRankOnePoleGateRejected

regressionThreeByThreePoleQuotient :
  Det3.SameSignedDeterminant
    (Det3.det3 Det3.response₁ Det3.response₂ Det3.poleProfile)
    (Det3.det3 Det3.residual₁ Det3.residual₂ Det3.poleProfile)
regressionThreeByThreePoleQuotient =
  Det3.augmentedPoleQuotientPreservesSignedDeterminant

regressionPairAdmission : Pair.PrimePairRelationalAdmission
regressionPairAdmission = Pair.canonicalToyPrimePairRelationalAdmission

regressionCrossPollinationObserver : Cross.newExteriorCoordinateReturned ≡ true
regressionCrossPollinationObserver = Cross.newExteriorCoordinateReturnedIsTrue

regressionRHBoundary :
  G21.G21CurrentBoundary.riemannHypothesisDerived
    G21.canonicalG21CurrentBoundary
  ≡ false
regressionRHBoundary =
  G21.G21CurrentBoundary.riemannHypothesisDerivedIsFalse
    G21.canonicalG21CurrentBoundary

module DASHI.Analysis.RiemannG21Regression where

import DASHI.Analysis.RiemannG21LiteralPoleRankAuditExact as PoleAudit
import DASHI.Analysis.RiemannG21PrimePairKernelExact as Pair
import DASHI.Analysis.RiemannG21TwoByTwoMixedObstructionExact as Mixed2
import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Det3
import DASHI.Analysis.RiemannG21PoleQuotientedExteriorExact as G21
import DASHI.Analysis.RiemannG21CrossPollinationExact as Cross

open import DASHI.Core.Prelude

regressionGenericThreeSampleResidualDimension :
  PoleAudit.residualDimension PoleAudit.genericTwoPoleThreeSampleCase ≡ 1
regressionGenericThreeSampleResidualDimension =
  G21.literalGenericThreeSampleResidualDimension

regressionRobustFourSampleResidualDimension :
  PoleAudit.residualDimension PoleAudit.genericTwoPoleFourSampleCase ≡ 2
regressionRobustFourSampleResidualDimension =
  G21.robustFourSampleResidualDimension

regressionTwoByTwoNoGo :
  Mixed2.det2Code Mixed2.responseLeft Mixed2.responseRight
  ≡ Mixed2.det2Code Mixed2.commonPole Mixed2.commonPole
  → ⊥
regressionTwoByTwoNoGo = G21.naiveTwoByTwoRankOnePoleGateRejected

regressionConditionalThreeByThreePoleQuotient :
  Det3.SameSignedDeterminant
    (Det3.det3 Det3.response₁ Det3.response₂ Det3.poleProfile)
    (Det3.det3 Det3.residual₁ Det3.residual₂ Det3.poleProfile)
regressionConditionalThreeByThreePoleQuotient =
  G21.finiteThreeByThreeRankOneMechanism

regressionPairAdmission : Pair.PrimePairRelationalAdmission
regressionPairAdmission = Pair.canonicalToyPrimePairRelationalAdmission

regressionCrossPollinationObserver :
  Cross.robustRankTwoExteriorCarrierReturned ≡ true
regressionCrossPollinationObserver =
  Cross.robustRankTwoExteriorCarrierReturnedIsTrue

regressionRankOneNotDerived :
  G21.G21CurrentBoundary.rankOnePoleReductionDerived
    G21.canonicalG21CurrentBoundary
  ≡ false
regressionRankOneNotDerived =
  G21.G21CurrentBoundary.rankOnePoleReductionDerivedIsFalse
    G21.canonicalG21CurrentBoundary

regressionRHBoundary :
  G21.G21CurrentBoundary.riemannHypothesisDerived
    G21.canonicalG21CurrentBoundary
  ≡ false
regressionRHBoundary =
  G21.G21CurrentBoundary.riemannHypothesisDerivedIsFalse
    G21.canonicalG21CurrentBoundary

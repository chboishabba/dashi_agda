module DASHI.PointedBulkSporadicTarotCabarlahRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.PointedTernaryBulkExact as Bulk
import DASHI.Biology.DecimalTenTernaryPresentationExact as Decimal
import DASHI.Biology.ReducedFiftyThreeOrbitCandidateExact as Orbit
import DASHI.Biology.SporadicTarotDependencyExact as Tarot
import DASHI.Biology.PointedBulkReducedMoonshineBoundary as Moonshine
import DASHI.Governance.CabarlahTraumaProjectionBridgeExact as Cabarlah
import DASHI.Governance.TraumaMemorySublationBoundary as Trauma
import DASHI.PointedBulkSporadicTarotCabarlahBoundary as Boundary

pointedBulkRegression : Bulk.pointedBulkDimension ≡ 196830
pointedBulkRegression = Bulk.pointedBulkDimensionIs196830

decimalBulkRegression : Decimal.decimalTernaryBulkDimension ≡ 196830
decimalBulkRegression = Decimal.decimalTernaryBulkDimensionIs196830

decimalPointedCountRegression :
  Decimal.decimalTernaryBulkDimension ≡ Bulk.pointedBulkDimension
decimalPointedCountRegression =
  Decimal.decimalAndPointedBulkDimensionsAgree

irrepOrientationTenRegression :
  Decimal.irrepOrientationSectorCount ≡ 10
irrepOrientationTenRegression = Decimal.irrepOrientationSectorCountIsTen

pointedBulkAlternativeRegression :
  Bulk.pointedBulkDimension
  ≡ Bulk.ternarySheetCount + Bulk.ternaryElevenCount
pointedBulkAlternativeRegression =
  Bulk.pointedBulkEqualsThreeNinePlusThreeEleven

pointedRotationRegression :
  (state : Bulk.PointedTernarySheet) →
  Bulk.rotatePointedFour state ≡ state
pointedRotationRegression = Bulk.rotatePointedFourReturns

pointedReflectionRegression :
  (state : Bulk.PointedTernarySheet) →
  Bulk.reflectPointedVertical (Bulk.reflectPointedVertical state) ≡ state
pointedReflectionRegression = Bulk.reflectionPointedIsInvolutive

pointedD4Regression : Bulk.pointedRepresentationDimension ≡ 10
pointedD4Regression = Bulk.pointedRepresentationDimensionIsTen

candidateResidualArithmeticRegression :
  Orbit.candidateR53Dimension ≡ 53
candidateResidualArithmeticRegression =
  Orbit.candidateR53DimensionIsFiftyThree

candidateInvolutionRegression :
  (state : Orbit.CandidateR53) →
  Orbit.candidateInvolution (Orbit.candidateInvolution state) ≡ state
candidateInvolutionRegression = Orbit.candidateInvolutionIsInvolutive

fullCoefficientRegression : Moonshine.fullCoefficientDimension ≡ 196884
fullCoefficientRegression = Moonshine.fullCoefficientDimensionIs196884

nontrivialCoefficientRegression :
  Moonshine.nontrivialCoefficientDimension ≡ 196883
nontrivialCoefficientRegression =
  Moonshine.nontrivialCoefficientDimensionIs196883

promotionOrderRegression :
  Moonshine.advanceSeven Moonshine.arithmeticCardinalityStage
  ≡ Moonshine.signTwistedModuleStage
promotionOrderRegression =
  Moonshine.signTwistOccursSevenPromotionsAfterArithmetic

sporadicInventoryRegression : Tarot.sporadicInventoryCount ≡ 26
sporadicInventoryRegression = Tarot.sporadicInventoryCountIsTwentySix

sporadicFamilyRegression : 5 + 7 + 8 + 6 ≡ 26
sporadicFamilyRegression = Tarot.familyCountsSumToTwentySix

co4Regression :
  Tarot.conwayCardReferent Tarot.Co4SyntheticCard ≡ Tarot.none
co4Regression = Tarot.co4HasNoConwaySporadicReferent

arcanaDeficitRegression : Tarot.inventoryMinusArcanaCount ≡ 4
arcanaDeficitRegression = Tarot.inventoryMinusArcanaCountIsFour

wittBlockRegression :
  Tarot.wittBlockCount * Tarot.sixChooseThree
  ≡ Tarot.twentyTwoChooseThree
wittBlockRegression = Tarot.wittBlockEquation

reflectingPoolMotiveRegression :
  Trauma.motiveInferredAsFact Trauma.reflectingPoolObservation ≡ false
reflectingPoolMotiveRegression =
  Cabarlah.reflectingPoolReadingDoesNotInferMotive

integratedBoundaryRegression :
  Boundary.PointedBulkSporadicTarotCabarlahBoundary
integratedBoundaryRegression =
  Boundary.canonicalPointedBulkSporadicTarotCabarlahBoundary

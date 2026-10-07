module DASHI.Governance.BoloBoloComparatorCalibrationFrontierRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact as Frontier

portoRegionsPinned :
  Frontier.portoAlegreRegionCount Frontier.canonicalComparatorStructuralCoordinates ≡ 16
portoRegionsPinned = refl

mondragonCooperativesPinned :
  Frontier.mondragonCooperativeCount Frontier.canonicalComparatorStructuralCoordinates ≡ 95
mondragonCooperativesPinned = refl

polycentricCasesPinned :
  Frontier.polycentricWaterCaseCount Frontier.canonicalComparatorStructuralCoordinates ≡ 26
polycentricCasesPinned = refl

allMechanismSurfacesPresent :
  Frontier.removedCouplingMechanismObservable Frontier.canonicalPrimitiveCalibrationFrontier ≡ true
  × Frontier.boundaryCoordinationMechanismObservable Frontier.canonicalPrimitiveCalibrationFrontier ≡ true
  × Frontier.delegationReportbackMechanismObservable Frontier.canonicalPrimitiveCalibrationFrontier ≡ true
  × Frontier.unresolvedConflictMechanismObservable Frontier.canonicalPrimitiveCalibrationFrontier ≡ true
allMechanismSurfacesPresent = refl , refl , refl , refl

targetWeightBoundsStillUnpaid :
  Frontier.targetQualifiedPerUnitWeightBoundsPaid Frontier.canonicalPrimitiveCalibrationFrontier ≡ false
targetWeightBoundsStillUnpaid = refl

spokesMinutesAreNextAcquisition :
  Frontier.acquireUnderlyingOWSSpokesMinutes Frontier.canonicalComparatorAcquisitionRoadmap ≡ true
spokesMinutesAreNextAcquisition = refl

holdoutStillProtected :
  Frontier.consumeHistoricalHoldoutBeforeDevelopmentGatePasses Frontier.canonicalComparatorAcquisitionRoadmap ≡ false
holdoutStillProtected = refl

comparatorsConstrainModelsNotCosts :
  Frontier.comparatorCasesCanConstrainPlausibleModelFamilies Frontier.canonicalComparatorCalibrationBoundary ≡ true
comparatorsConstrainModelsNotCosts = refl

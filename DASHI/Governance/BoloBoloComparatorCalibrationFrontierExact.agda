module DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt

record ComparatorStructuralCoordinates : Set where
  constructor comparatorStructuralCoordinates
  field
    portoAlegreRegionCount : Nat
    portoAlegreApproxDelegateForumCount : Nat
    portoAlegreCouncilCount : Nat
    mondragonCooperativeCount : Nat
    mondragonCongressRepresentativeCount : Nat
    mondragonBroadAreaCount : Nat
    mondragonIndustrialDivisionCount : Nat
    mondragonSocialCouncilMembersPerRepresentativeLower : Nat
    mondragonSocialCouncilMembersPerRepresentativeUpper : Nat
    polycentricWaterCaseCount : Nat
    empiricalPolycentricReviewCount : Nat
    empiricalPolycentricCoreCount : Nat

open ComparatorStructuralCoordinates public

canonicalComparatorStructuralCoordinates : ComparatorStructuralCoordinates
canonicalComparatorStructuralCoordinates =
  comparatorStructuralCoordinates
    16 1000 44
    95 650 4 13 25 30
    26 179 112

record ComparatorWorkloadCoordinates : Set where
  constructor comparatorWorkloadCoordinates
  field
    portoAlegreCouncilMembers : Nat
    portoAlegreCouncilMeetingMinutesPerWeekLowerBound : Nat
    portoAlegreCouncilPersonMinutesPerWeekLowerBound : Nat
    mondragonManagementReportbacksPerMonthLowerBound : Nat
    portoTimingIsWholeDelegationCost : Bool
    mondragonMonthlyReportIsWholeDelegationCost : Bool
    comparatorCadenceAutomaticallyTransfersToBolo : Bool

open ComparatorWorkloadCoordinates public

canonicalComparatorWorkloadCoordinates : ComparatorWorkloadCoordinates
canonicalComparatorWorkloadCoordinates =
  comparatorWorkloadCoordinates 44 120 5280 1 false false false

portoCouncilPersonMinutesArithmetic : 44 * 120 ≡ 5280
portoCouncilPersonMinutesArithmetic = refl

record PrimitiveCalibrationFrontier : Set where
  constructor primitiveCalibrationFrontier
  field
    removedCouplingMechanismObservable : Bool
    boundaryCoordinationMechanismObservable : Bool
    delegationReportbackMechanismObservable : Bool
    unresolvedConflictMechanismObservable : Bool
    sameContextFlatNestedTransitionObserved : Bool
    durableNestedFederationObserved : Bool
    largeUrbanNestedParticipationObserved : Bool
    comparativeDecentralisationPlusCoordinationPerformanceObserved : Bool
    positiveAndNegativePolycentricOutcomesObservedAcrossLiterature : Bool
    comparatorGovernanceCadenceMeasured : Bool
    comparatorLocalPositiveGovernanceWorkloadObserved : Bool
    institutionalVersionChangeObserved : Bool
    targetQualifiedRemovedCostLowerBoundPaid : Bool
    targetQualifiedBoundaryCostUpperBoundPaid : Bool
    targetQualifiedDelegationCostUpperBoundPaid : Bool
    targetQualifiedUnresolvedCostUpperBoundPaid : Bool
    targetQualifiedPerUnitWeightBoundsPaid : Bool
    robustMeaningfulBoloWinOrLossPaid : Bool

open PrimitiveCalibrationFrontier public

canonicalPrimitiveCalibrationFrontier : PrimitiveCalibrationFrontier
canonicalPrimitiveCalibrationFrontier =
  primitiveCalibrationFrontier
    true true true true
    true true true true true true true true
    false false false false false false

record ComparatorAcquisitionRoadmap : Set where
  constructor comparatorAcquisitionRoadmap
  field
    acquireUnderlyingOWSSpokesMinutes : Bool
    extractSameProcessObservablesFromSpokesMinutes : Bool
    preserveExistingGAHoldout : Bool
    modelEvictionAndTimeTrendAsTransitionConfounds : Bool
    acquireAdditionalPortoAlegrePreparationAndDelegateWorkload : Bool
    acquireAdditionalMondragonMeetingDurationAndPreparationWorkload : Bool
    keepComparatorVersionsSeparate : Bool
    useCrossCaseEvidenceToPredeclareAdmissibleModelFamily : Bool
    consumeHistoricalHoldoutBeforeDevelopmentGatePasses : Bool
    runDirectFlatNestedPilotIfObservationalBoundsRemainNonIdentifying : Bool

open ComparatorAcquisitionRoadmap public

canonicalComparatorAcquisitionRoadmap : ComparatorAcquisitionRoadmap
canonicalComparatorAcquisitionRoadmap =
  comparatorAcquisitionRoadmap true true true true true true true true false true

record ComparatorCalibrationBoundary : Set where
  constructor comparatorCalibrationBoundary
  field
    delegateCountEqualsDelegationCost : Bool
    representativeRatioEqualsEfficiency : Bool
    institutionalLongevityEqualsSuperiority : Bool
    governanceCadenceEqualsTotalCoordinationCost : Bool
    comparatorLocalPersonMinutesEqualTargetBoloCost : Bool
    historicalAndCurrentInstitutionalCoordinatesCanBeSpliced : Bool
    crossDomainCoordinationPerformanceEqualsBoloCost : Bool
    comparatorCasesCanConstrainPlausibleModelFamilies : Bool
    sameContextSpokesTransitionHasHighestHistoricalDesignRelevance : Bool
    numericalTargetBoundsStillRequireNewMeasurementOrTransport : Bool

open ComparatorCalibrationBoundary public

canonicalComparatorCalibrationBoundary : ComparatorCalibrationBoundary
canonicalComparatorCalibrationBoundary =
  comparatorCalibrationBoundary false false false false false false false true true true

canonicalComparatorCalibrationFrontierReceipt : GenericReceipt.GenericReceipt
canonicalComparatorCalibrationFrontierReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo real-world comparator calibration frontier"
    "DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact"
    "canonicalComparatorStructuralCoordinates / canonicalComparatorWorkloadCoordinates / canonicalPrimitiveCalibrationFrontier / canonicalComparatorAcquisitionRoadmap / canonicalComparatorCalibrationBoundary"
    "records source-paid scale and governance-cadence coordinates from Porto Alegre and Mondragon plus comparative polycentric-governance case counts; derives the comparator-local historical Porto Alegre floor of 5280 council-person-minutes per week and records that comparator institutional architecture changes over time"
    "the workload floor covers only the cited council layer, is not a target bolo cost or per-unit coefficient, and historical/current institutional coordinates cannot be silently combined; target-qualified primitive bounds still require direct measurement or an explicit transport argument, while primary OWS Spokes minutes and richer preparation/reportback workload remain the highest-value acquisitions"
    "agda -i . DASHI/Governance/BoloBoloComparatorCalibrationFrontierRegression.agda"

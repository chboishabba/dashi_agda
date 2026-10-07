module DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloComparatorEvidenceAtlasExact as Atlas
import DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact as Spokes
import DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact as Synthesis

------------------------------------------------------------------------
-- STRUCTURAL COORDINATES FROM REAL COMPARATORS.
--
-- These are source-paid institutional counts or case counts.  They are useful
-- for checking scale/feasibility and designing measurements, but none is a
-- coordination-cost coefficient or a target-qualified bolo bound.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- SOURCE-EXPLICIT GOVERNANCE WORKLOAD / CADENCE COORDINATES.
--
-- Porto Alegre: the 44-member COP met for at least two hours weekly during the
-- July-September budget phase in the cited historical case description.
-- Mondragon: an individual cooperative's Management Council reports to its
-- elected Governing Council at least monthly in the cited 2023 case study.
--
-- These are process-cadence lower bounds in their own contexts. They are not
-- total coordination cost, do not include preparation/reportback outside the
-- meeting, and do not transport automatically to a bolo target.
------------------------------------------------------------------------

record ComparatorWorkloadCoordinates : Set where
  constructor comparatorWorkloadCoordinates
  field
    portoAlegreCouncilMembers : Nat
    portoAlegreCouncilMeetingMinutesPerWeekLowerBound : Nat
    mondragonManagementReportbacksPerMonthLowerBound : Nat
    portoTimingIsWholeDelegationCost : Bool
    mondragonMonthlyReportIsWholeDelegationCost : Bool
    comparatorCadenceAutomaticallyTransfersToBolo : Bool

open ComparatorWorkloadCoordinates public

canonicalComparatorWorkloadCoordinates : ComparatorWorkloadCoordinates
canonicalComparatorWorkloadCoordinates =
  comparatorWorkloadCoordinates 44 120 1 false false false

------------------------------------------------------------------------
-- Primitive-term calibration frontier.
------------------------------------------------------------------------

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
    true true true true true true
    false false false false false false

------------------------------------------------------------------------
-- Acquisition ordering after the comparator pass.
------------------------------------------------------------------------

record ComparatorAcquisitionRoadmap : Set where
  constructor comparatorAcquisitionRoadmap
  field
    acquireUnderlyingOWSSpokesMinutes : Bool
    extractSameProcessObservablesFromSpokesMinutes : Bool
    preserveExistingGAHoldout : Bool
    modelEvictionAndTimeTrendAsTransitionConfounds : Bool
    acquireAdditionalPortoAlegreProcessTimingAndDelegateWorkload : Bool
    acquireAdditionalMondragonGovernanceTransactionWorkload : Bool
    useCrossCaseEvidenceToPredeclareAdmissibleModelFamily : Bool
    consumeHistoricalHoldoutBeforeDevelopmentGatePasses : Bool
    runDirectFlatNestedPilotIfObservationalBoundsRemainNonIdentifying : Bool

open ComparatorAcquisitionRoadmap public

canonicalComparatorAcquisitionRoadmap : ComparatorAcquisitionRoadmap
canonicalComparatorAcquisitionRoadmap =
  comparatorAcquisitionRoadmap true true true true true true true false true

record ComparatorCalibrationBoundary : Set where
  constructor comparatorCalibrationBoundary
  field
    delegateCountEqualsDelegationCost : Bool
    representativeRatioEqualsEfficiency : Bool
    institutionalLongevityEqualsSuperiority : Bool
    governanceCadenceEqualsTotalCoordinationCost : Bool
    crossDomainCoordinationPerformanceEqualsBoloCost : Bool
    comparatorCasesCanConstrainPlausibleModelFamilies : Bool
    sameContextSpokesTransitionHasHighestHistoricalDesignRelevance : Bool
    numericalTargetBoundsStillRequireNewMeasurement : Bool

open ComparatorCalibrationBoundary public

canonicalComparatorCalibrationBoundary : ComparatorCalibrationBoundary
canonicalComparatorCalibrationBoundary =
  comparatorCalibrationBoundary false false false false false true true true

canonicalComparatorCalibrationFrontierReceipt : GenericReceipt.GenericReceipt
canonicalComparatorCalibrationFrontierReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo real-world comparator calibration frontier"
    "DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact"
    "canonicalComparatorStructuralCoordinates / canonicalComparatorWorkloadCoordinates / canonicalPrimitiveCalibrationFrontier / canonicalComparatorAcquisitionRoadmap / canonicalComparatorCalibrationBoundary"
    "records source-paid scale and governance-cadence coordinates from Porto Alegre and Mondragon plus comparative polycentric-governance case counts; all four mechanism surfaces now have real-world comparators, including a same-context OWS flat-to-Spokes transition, durable multi-level federation, large urban nested participation and comparative decentralisation-plus-coordination performance"
    "Porto Alegre's at-least-two-hours-per-week council cadence and Mondragon's at-least-monthly management-to-governing-council reportback are comparator-specific workload observations rather than total coordination costs or transferable bolo bounds; the next historical acquisition remains the underlying OWS Spokes minutes while the protected GA holdout stays unspent"
    "agda -i . DASHI/Governance/BoloBoloComparatorCalibrationFrontierRegression.agda"

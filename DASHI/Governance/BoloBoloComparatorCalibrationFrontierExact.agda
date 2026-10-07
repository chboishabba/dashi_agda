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
    true true true true true
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
    acquirePortoAlegreProcessTimingAndDelegateWorkloadIfAvailable : Bool
    acquireMondragonGovernanceTransactionWorkloadIfAvailable : Bool
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
    crossDomainCoordinationPerformanceEqualsBoloCost : Bool
    comparatorCasesCanConstrainPlausibleModelFamilies : Bool
    sameContextSpokesTransitionHasHighestHistoricalDesignRelevance : Bool
    numericalTargetBoundsStillRequireNewMeasurement : Bool

open ComparatorCalibrationBoundary public

canonicalComparatorCalibrationBoundary : ComparatorCalibrationBoundary
canonicalComparatorCalibrationBoundary =
  comparatorCalibrationBoundary false false false false true true true

canonicalComparatorCalibrationFrontierReceipt : GenericReceipt.GenericReceipt
canonicalComparatorCalibrationFrontierReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo real-world comparator calibration frontier"
    "DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact"
    "canonicalComparatorStructuralCoordinates / canonicalPrimitiveCalibrationFrontier / canonicalComparatorAcquisitionRoadmap / canonicalComparatorCalibrationBoundary"
    "records source-paid scale coordinates from Porto Alegre, Mondragon and comparative polycentric-governance studies and classifies the evidence frontier: all four mechanism surfaces now have real-world comparators, including a same-context OWS flat-to-Spokes transition, durable multi-level federation and comparative decentralisation-plus-coordination performance"
    "none of the institutional counts is a cost coefficient or efficiency ratio and no target-qualified primitive cost or per-unit weight bound is yet paid; the next historical acquisition is the underlying OWS Spokes minutes while the existing GA holdout remains protected, followed by direct target experimentation if observational bounds remain non-identifying"
    "agda -i . DASHI/Governance/BoloBoloComparatorCalibrationFrontierRegression.agda"

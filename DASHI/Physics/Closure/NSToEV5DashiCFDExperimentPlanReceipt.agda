module DASHI.Physics.Closure.NSToEV5DashiCFDExperimentPlanReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Combinatorics.FractranCOL as FractranCOL

------------------------------------------------------------------------
-- dashiCFD numerical experiment plan for the NS-to-EV5 projection.
--
-- Boundary:
-- This is an experiment-plan receipt only.  It records that the sibling
-- ../dashiCFD surface can generate 2D vorticity / LES enstrophy traces,
-- that dyadic shell enstrophy E_j(t) can be extracted from snapshots, and
-- that those traces can be used to falsify a top-five-shell EV5 candidate
-- against Q monotonicity, r17 diagnostics, and resonant forcing cycles.
-- It is evidence only, not proof; 2D CFD does not prove 3D Navier-Stokes
-- regularity.

data NSToEV5DashiCFDExperimentStatus : Set where
  numericalEvidencePlanOnly_noNSToEV5Proof_noClayPromotion :
    NSToEV5DashiCFDExperimentStatus

data DashiCFDTraceSource : Set where
  truthSnapshotOmegaTrace :
    DashiCFDTraceSource

  twoDVorticityCodecTrace :
    DashiCFDTraceSource

  lesDyadicShellEnstrophyTrace :
    DashiCFDTraceSource

  gpuLESEnstrophyCSVTrace :
    DashiCFDTraceSource

  v4SnapshotMetricsTrace :
    DashiCFDTraceSource

canonicalDashiCFDTraceSources :
  List DashiCFDTraceSource
canonicalDashiCFDTraceSources =
  truthSnapshotOmegaTrace
  ∷ twoDVorticityCodecTrace
  ∷ lesDyadicShellEnstrophyTrace
  ∷ gpuLESEnstrophyCSVTrace
  ∷ v4SnapshotMetricsTrace
  ∷ []

data DashiCFDExperimentScript : Set where
  scriptsMakeTruthPy :
    DashiCFDExperimentScript

  runLESGPUPy :
    DashiCFDExperimentScript

  runV4SnapshotsPy :
    DashiCFDExperimentScript

  dashiLESVorticityCodecPy :
    DashiCFDExperimentScript

  dashiLESVorticityCodecV2Py :
    DashiCFDExperimentScript

  scriptsPlotEnstrophyPy :
    DashiCFDExperimentScript

canonicalDashiCFDExperimentScripts :
  List DashiCFDExperimentScript
canonicalDashiCFDExperimentScripts =
  scriptsMakeTruthPy
  ∷ runLESGPUPy
  ∷ runV4SnapshotsPy
  ∷ dashiLESVorticityCodecPy
  ∷ dashiLESVorticityCodecV2Py
  ∷ scriptsPlotEnstrophyPy
  ∷ []

data ExtractedObservable : Set where
  dyadicShellDepth :
    ExtractedObservable

  shellEnstrophyEjOfT :
    ExtractedObservable

  topFiveShellIndicesByEnstrophy :
    ExtractedObservable

  totalShellEnstrophyNormalizationGuard :
    ExtractedObservable

  totalEnstrophyTrace :
    ExtractedObservable

  adjacentShellTransferProxy :
    ExtractedObservable

  qTraceObservable :
    ExtractedObservable

  forcingPhaseAndCycleWitness :
    ExtractedObservable

canonicalExtractedObservables :
  List ExtractedObservable
canonicalExtractedObservables =
  dyadicShellDepth
  ∷ shellEnstrophyEjOfT
  ∷ topFiveShellIndicesByEnstrophy
  ∷ totalShellEnstrophyNormalizationGuard
  ∷ totalEnstrophyTrace
  ∷ adjacentShellTransferProxy
  ∷ qTraceObservable
  ∷ forcingPhaseAndCycleWitness
  ∷ []

data EV5CandidateLane : Set where
  lane2ActiveDyadicDepthJMax :
    EV5CandidateLane

  lane3AdjacentCascadeRatio :
    EV5CandidateLane

  lane5SecondaryShellOccupancy :
    EV5CandidateLane

  lane7PeakShellEnstrophyFraction :
    EV5CandidateLane

  lane11Z3PhaseCoherenceProxy :
    EV5CandidateLane

canonicalEV5CandidateLanes :
  List EV5CandidateLane
canonicalEV5CandidateLanes =
  lane2ActiveDyadicDepthJMax
  ∷ lane3AdjacentCascadeRatio
  ∷ lane5SecondaryShellOccupancy
  ∷ lane7PeakShellEnstrophyFraction
  ∷ lane11Z3PhaseCoherenceProxy
  ∷ []

data NumericalCheck : Set where
  qMonotonicityAfterBurnIn :
    NumericalCheck

  r17TailLaneDescent :
    NumericalCheck

  resonantForcingCycleLockTest :
    NumericalCheck

  shellEnstrophyContradictionCheck :
    NumericalCheck

  falsificationRulePreservesFailures :
    NumericalCheck

  stabilityAcrossSeedsGridsBackends :
    NumericalCheck

canonicalNumericalChecks :
  List NumericalCheck
canonicalNumericalChecks =
  qMonotonicityAfterBurnIn
  ∷ r17TailLaneDescent
  ∷ resonantForcingCycleLockTest
  ∷ shellEnstrophyContradictionCheck
  ∷ falsificationRulePreservesFailures
  ∷ stabilityAcrossSeedsGridsBackends
  ∷ []

data ProofPromotionToken : Set where

promotionImpossibleHere :
  ProofPromotionToken →
  ⊥
promotionImpossibleHere ()

dashiCFDRelativePath :
  String
dashiCFDRelativePath =
  "../dashiCFD"

experimentPlanDocPath :
  String
experimentPlanDocPath =
  "Docs/NSToEV5DashiCFDExperimentPlan.md"

evidenceBoundaryStatement :
  String
evidenceBoundaryStatement =
  "dashiCFD 2D shell-enstrophy traces are numerical evidence only; they may falsify a candidate encoding but do not prove the NS-to-EV5 projection or 3D Navier-Stokes regularity."

shellEnstrophyObservableName :
  String
shellEnstrophyObservableName =
  "E_j(t)"

qMonotonicityObservableName :
  String
qMonotonicityObservableName =
  "Q(t)"

record NSToEV5DashiCFDExperimentPlanReceipt : Set₁ where
  field
    status :
      NSToEV5DashiCFDExperimentStatus

    statusIsPlanOnly :
      status
      ≡
      numericalEvidencePlanOnly_noNSToEV5Proof_noClayPromotion

    planDocument :
      String

    planDocumentIsCanonical :
      planDocument ≡ experimentPlanDocPath

    siblingRepository :
      String

    siblingRepositoryIsDashiCFD :
      siblingRepository ≡ dashiCFDRelativePath

    traceSources :
      List DashiCFDTraceSource

    traceSourcesAreCanonical :
      traceSources ≡ canonicalDashiCFDTraceSources

    dashiCFDScripts :
      List DashiCFDExperimentScript

    dashiCFDScriptsAreCanonical :
      dashiCFDScripts ≡ canonicalDashiCFDExperimentScripts

    extractedObservables :
      List ExtractedObservable

    extractedObservablesAreCanonical :
      extractedObservables ≡ canonicalExtractedObservables

    evCarrier :
      Set

    evCarrierIsFractranEV5 :
      evCarrier ≡ FractranCOL.EV5

    carrierPrimeLanes :
      List Nat

    carrierPrimeLanesAreCanonical :
      carrierPrimeLanes ≡ (2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ [])

    candidateLanes :
      List EV5CandidateLane

    candidateLanesAreCanonical :
      candidateLanes ≡ canonicalEV5CandidateLanes

    fractranRuleUnderTailCheck :
      FractranCOL.Rule

    fractranRuleUnderTailCheckIsR17 :
      fractranRuleUnderTailCheck ≡ FractranCOL.r17

    fractranEnergy :
      FractranCOL.EV5 → Nat

    fractranEnergyIsCanonical :
      fractranEnergy ≡ FractranCOL.E

    energyActivePrimeLanes :
      List Nat

    energyActivePrimeLanesAreCanonical :
      energyActivePrimeLanes ≡ (2 ∷ 3 ∷ 7 ∷ [])

    numericalChecks :
      List NumericalCheck

    numericalChecksAreCanonical :
      numericalChecks ≡ canonicalNumericalChecks

    shellEnstrophyObservable :
      String

    shellEnstrophyObservableIsEjOfT :
      shellEnstrophyObservable ≡ shellEnstrophyObservableName

    topFiveShellEV5EncodingPlanned :
      Bool

    topFiveShellEV5EncodingPlannedIsTrue :
      topFiveShellEV5EncodingPlanned ≡ true

    qMonotonicityObservable :
      String

    qMonotonicityObservableIsCanonical :
      qMonotonicityObservable ≡ qMonotonicityObservableName

    qMonotonicityTestIncluded :
      Bool

    qMonotonicityTestIncludedIsTrue :
      qMonotonicityTestIncluded ≡ true

    resonantForcingCycleTestIncluded :
      Bool

    resonantForcingCycleTestIncludedIsTrue :
      resonantForcingCycleTestIncluded ≡ true

    falsificationRuleIncluded :
      Bool

    falsificationRuleIncludedIsTrue :
      falsificationRuleIncluded ≡ true

    dashiCFDCanGenerateTraces :
      Bool

    dashiCFDCanGenerateTracesIsTrue :
      dashiCFDCanGenerateTraces ≡ true

    ev5CandidateEncodingPlanned :
      Bool

    ev5CandidateEncodingPlannedIsTrue :
      ev5CandidateEncodingPlanned ≡ true

    monotonicityAndNonresonanceChecksIncluded :
      Bool

    monotonicityAndNonresonanceChecksIncludedIsTrue :
      monotonicityAndNonresonanceChecksIncluded ≡ true

    evidenceOnly :
      Bool

    evidenceOnlyIsTrue :
      evidenceOnly ≡ true

    nsToEV5ProjectionProvedHere :
      Bool

    nsToEV5ProjectionProvedHereIsFalse :
      nsToEV5ProjectionProvedHere ≡ false

    threeDimensionalNSProvedBy2DCFD :
      Bool

    threeDimensionalNSProvedBy2DCFDIsFalse :
      threeDimensionalNSProvedBy2DCFD ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    proofPromotionTokens :
      List ProofPromotionToken

    proofPromotionTokensAreEmpty :
      proofPromotionTokens ≡ []

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ evidenceBoundaryStatement

open NSToEV5DashiCFDExperimentPlanReceipt public

canonicalNSToEV5DashiCFDExperimentPlanReceipt :
  NSToEV5DashiCFDExperimentPlanReceipt
canonicalNSToEV5DashiCFDExperimentPlanReceipt =
  record
    { status =
        numericalEvidencePlanOnly_noNSToEV5Proof_noClayPromotion
    ; statusIsPlanOnly =
        refl
    ; planDocument =
        experimentPlanDocPath
    ; planDocumentIsCanonical =
        refl
    ; siblingRepository =
        dashiCFDRelativePath
    ; siblingRepositoryIsDashiCFD =
        refl
    ; traceSources =
        canonicalDashiCFDTraceSources
    ; traceSourcesAreCanonical =
        refl
    ; dashiCFDScripts =
        canonicalDashiCFDExperimentScripts
    ; dashiCFDScriptsAreCanonical =
        refl
    ; extractedObservables =
        canonicalExtractedObservables
    ; extractedObservablesAreCanonical =
        refl
    ; evCarrier =
        FractranCOL.EV5
    ; evCarrierIsFractranEV5 =
        refl
    ; carrierPrimeLanes =
        2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ []
    ; carrierPrimeLanesAreCanonical =
        refl
    ; candidateLanes =
        canonicalEV5CandidateLanes
    ; candidateLanesAreCanonical =
        refl
    ; fractranRuleUnderTailCheck =
        FractranCOL.r17
    ; fractranRuleUnderTailCheckIsR17 =
        refl
    ; fractranEnergy =
        FractranCOL.E
    ; fractranEnergyIsCanonical =
        refl
    ; energyActivePrimeLanes =
        2 ∷ 3 ∷ 7 ∷ []
    ; energyActivePrimeLanesAreCanonical =
        refl
    ; numericalChecks =
        canonicalNumericalChecks
    ; numericalChecksAreCanonical =
        refl
    ; shellEnstrophyObservable =
        shellEnstrophyObservableName
    ; shellEnstrophyObservableIsEjOfT =
        refl
    ; topFiveShellEV5EncodingPlanned =
        true
    ; topFiveShellEV5EncodingPlannedIsTrue =
        refl
    ; qMonotonicityObservable =
        qMonotonicityObservableName
    ; qMonotonicityObservableIsCanonical =
        refl
    ; qMonotonicityTestIncluded =
        true
    ; qMonotonicityTestIncludedIsTrue =
        refl
    ; resonantForcingCycleTestIncluded =
        true
    ; resonantForcingCycleTestIncludedIsTrue =
        refl
    ; falsificationRuleIncluded =
        true
    ; falsificationRuleIncludedIsTrue =
        refl
    ; dashiCFDCanGenerateTraces =
        true
    ; dashiCFDCanGenerateTracesIsTrue =
        refl
    ; ev5CandidateEncodingPlanned =
        true
    ; ev5CandidateEncodingPlannedIsTrue =
        refl
    ; monotonicityAndNonresonanceChecksIncluded =
        true
    ; monotonicityAndNonresonanceChecksIncludedIsTrue =
        refl
    ; evidenceOnly =
        true
    ; evidenceOnlyIsTrue =
        refl
    ; nsToEV5ProjectionProvedHere =
        false
    ; nsToEV5ProjectionProvedHereIsFalse =
        refl
    ; threeDimensionalNSProvedBy2DCFD =
        false
    ; threeDimensionalNSProvedBy2DCFDIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; proofPromotionTokens =
        []
    ; proofPromotionTokensAreEmpty =
        refl
    ; boundaryStatement =
        evidenceBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    }

experimentRemainsEvidenceOnly :
  evidenceOnly canonicalNSToEV5DashiCFDExperimentPlanReceipt ≡ true
experimentRemainsEvidenceOnly =
  refl

experimentDoesNotProveProjection :
  nsToEV5ProjectionProvedHere
    canonicalNSToEV5DashiCFDExperimentPlanReceipt
  ≡
  false
experimentDoesNotProveProjection =
  refl

experimentDoesNotPromoteClayNS :
  clayNavierStokesPromoted
    canonicalNSToEV5DashiCFDExperimentPlanReceipt
  ≡
  false
experimentDoesNotPromoteClayNS =
  refl

experimentIncludesQMonotonicityTest :
  qMonotonicityTestIncluded
    canonicalNSToEV5DashiCFDExperimentPlanReceipt
  ≡
  true
experimentIncludesQMonotonicityTest =
  refl

experimentIncludesResonantForcingCycleTest :
  resonantForcingCycleTestIncluded
    canonicalNSToEV5DashiCFDExperimentPlanReceipt
  ≡
  true
experimentIncludesResonantForcingCycleTest =
  refl

experimentIncludesFalsificationRule :
  falsificationRuleIncluded
    canonicalNSToEV5DashiCFDExperimentPlanReceipt
  ≡
  true
experimentIncludesFalsificationRule =
  refl

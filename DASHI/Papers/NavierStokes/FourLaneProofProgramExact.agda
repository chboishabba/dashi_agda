module DASHI.Papers.NavierStokes.FourLaneProofProgramExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as Four
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as S0
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyPointwiseExact as S1a
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as S1b

------------------------------------------------------------------------
-- NAVIER-STOKES A/B/C/D PAPER/PROGRAMME ADAPTER
--
-- Timestamp: 2026-09-15 18:55 AEST (UTC+10).
--
-- This file deliberately DOES NOT introduce a second four-alternative
-- ontology. The canonical mathematical/source alternatives already live in
-- NSClayFourAlternativeReleasedProofBidiExact. This owner only adds the
-- current Paper-1 route selection, historical/provenance status, explicit
-- A<->B transfer guards, and the current coordinator-level recovery state.
--
-- IMPORTANT: branch-recovery/source status is not certification. In
-- particular, a source-written conditional compiler does not become an
-- unconditional theorem or an observed commit-specific Agda kernel receipt.
------------------------------------------------------------------------

NSClayLane : Set
NSClayLane = Four.ClayAlternative4

wholeSpaceA : NSClayLane
wholeSpaceA = Four.A-euclidean-unforced-global

periodicB : NSClayLane
periodicB = Four.B-periodic-unforced-global

forcedWholeSpaceC : NSClayLane
forcedWholeSpaceC = Four.C-euclidean-forced-breakdown

forcedPeriodicD : NSClayLane
forcedPeriodicD = Four.D-periodic-forced-breakdown

record NSFourLaneProofProgram : Set where
  constructor ns-four-lane-proof-program
  field
    laneA laneB laneC laneD : NSClayLane

    statusA statusB statusC statusD : Four.AlternativeStatusReceipt4

    laneADescription : String
    laneBDescription : String
    laneCDescription : String
    laneDDescription : String

    periodicBIsActiveConstruction : Bool
    wholeSpaceAIsIndependentObligation : Bool
    forcedCDIsVerificationAndProvenance : Bool

    r571CenteredTaylorSixThreeR568IsPeriodicB : Bool
    periodicBR571TaylorRealizationClosed : Bool
    periodicBSecondMomentSixThreeTransplantClosed : Bool
    periodicBR568PaymentClosed : Bool

    periodicBCommutatorSpineRecoveryAssumptionActive : Bool
    periodicBCommutatorSpineCertificationObserved : Bool

    periodicBPhaseR104CompilerRecovered : Bool
    periodicBPhaseLiteralR406RemainderWeldRecovered : Bool
    periodicBPhaseCriticalRadialRealizationRecovered : Bool

    periodicBPhaseLiteralFiniteCriticalObservableFoldRecovered : Bool
    periodicBPhasePointwiseCriticalEnergySplitRecovered : Bool
    periodicBPhaseLiteralModeListCarrierRecovered : Bool
    periodicBPhaseCriticalEnergyCompilerGivenCalculusRecovered : Bool
    periodicBPhaseConcreteScalarFTCObserved : Bool
    periodicBPhaseConcreteIntegrationLinearityObserved : Bool
    periodicBPhaseR414ProductionNormalisationRecovered : Bool

    periodicBPhasePhysicalCriticalObservableRealizationRecovered : Bool
    periodicBPhaseCriticalEnergyInequalityRecovered : Bool
    periodicBPhaseSignedProductionEstimateRecovered : Bool
    periodicBPhaseUniformInitialCriticalCeilingRecovered : Bool
    periodicBPhasePositiveRetainedViscosityRecovered : Bool
    periodicBPhasePhysicalR104Recovered : Bool

    periodicBOnlyPhaseDiscoveryRemainsUnderCommRecoveryAssumption : Bool
    wholeSpaceADeferredUntilPeriodicPortabilityAudit : Bool

    wholeSpaceACurrentTerminalCutFrozen : Bool

    periodicBToWholeSpaceATransferConstructed : Bool
    wholeSpaceAToPeriodicBTransferConstructed : Bool
    periodicBProofProgressDoesNotPromoteWholeSpaceA : Bool
    wholeSpaceAProofProgressDoesNotPromotePeriodicB : Bool
    forcedCDDoesNotSettleUnforcedAB : Bool

    gramP3AttemptRetainedAsHistoricalProvenance : Bool
    gramP3AttemptAbandonedAsPrimaryRoute : Bool
    gramP3AbandonmentReason : String

open NSFourLaneProofProgram public

canonicalNSFourLaneProofProgram : NSFourLaneProofProgram
canonicalNSFourLaneProofProgram = record
  { laneA = wholeSpaceA
  ; laneB = periodicB
  ; laneC = forcedWholeSpaceC
  ; laneD = forcedPeriodicD
  ; statusA = Four.statusA4
  ; statusB = Four.statusB4
  ; statusC = Four.statusC4
  ; statusD = Four.statusD4
  ; laneADescription =
      "Lane A: unforced three-dimensional Navier-Stokes regularity on whole-space R^3. Independent proof obligation; defer new proof search until periodic-B stabilizes enough for an explicit portability quotient."
  ; laneBDescription =
      "Lane B: unforced three-dimensional periodic Navier-Stokes regularity on T^3. The recent commutator spine is routed as recovery/certification. R104/R372/R414 recover the signed-critical compiler and literal-R406 remainder identity; R516/R517 recover finite-carrier critical radial realization. S0 constructs the live finite critical fold, S1a closes the finite R30 pointwise energy split, and S1b compiles the integrated energy identity given explicit scalar FTC and integration-linearity authorities. Those concrete calculus authorities remain absent, so unconditional S1 and the later phase estimate, initial ceiling and retained-viscosity receipt remain fail-closed."
  ; laneCDescription =
      "Lane C: forced whole-space R^3 breakdown. Current job is released-proof BIDI verification, provenance, dependency closure, and same-object integration; it is not discovery evidence for A or B."
  ; laneDDescription =
      "Lane D: forced periodic T^3 breakdown. Current job is released-proof BIDI verification, provenance, dependency closure, same-object integration, and typed donor mining for periodic lemmas; it does not settle B."
  ; periodicBIsActiveConstruction = true
  ; wholeSpaceAIsIndependentObligation = true
  ; forcedCDIsVerificationAndProvenance = true
  ; r571CenteredTaylorSixThreeR568IsPeriodicB = true
  ; periodicBR571TaylorRealizationClosed = false
  ; periodicBSecondMomentSixThreeTransplantClosed = false
  ; periodicBR568PaymentClosed = false

  ; periodicBCommutatorSpineRecoveryAssumptionActive = true
  ; periodicBCommutatorSpineCertificationObserved = false

  ; periodicBPhaseR104CompilerRecovered = true
  ; periodicBPhaseLiteralR406RemainderWeldRecovered = true
  ; periodicBPhaseCriticalRadialRealizationRecovered = true

  ; periodicBPhaseLiteralFiniteCriticalObservableFoldRecovered =
      S0.literalCriticalEndpointFoldConstructed
  ; periodicBPhasePointwiseCriticalEnergySplitRecovered =
      S1a.literalFiniteCriticalEnergySplitClosed
  ; periodicBPhaseLiteralModeListCarrierRecovered =
      ModeCarrier.literalModeListConstancyWithoutViscosity
  ; periodicBPhaseCriticalEnergyCompilerGivenCalculusRecovered =
      S1b.integratedCriticalEnergyCompilerClosedGivenCalculus
  ; periodicBPhaseConcreteScalarFTCObserved =
      S1b.concreteScalarFTCInstalled
  ; periodicBPhaseConcreteIntegrationLinearityObserved =
      S1b.concreteIntegrationLinearityInstalled
  ; periodicBPhaseR414ProductionNormalisationRecovered =
      S0.r414ProductionNormalisationRecovered

  ; periodicBPhasePhysicalCriticalObservableRealizationRecovered = false
  ; periodicBPhaseCriticalEnergyInequalityRecovered = false
  ; periodicBPhaseSignedProductionEstimateRecovered = false
  ; periodicBPhaseUniformInitialCriticalCeilingRecovered = false
  ; periodicBPhasePositiveRetainedViscosityRecovered = false
  ; periodicBPhasePhysicalR104Recovered = false

  ; periodicBOnlyPhaseDiscoveryRemainsUnderCommRecoveryAssumption = true
  ; wholeSpaceADeferredUntilPeriodicPortabilityAudit = true

  ; wholeSpaceACurrentTerminalCutFrozen = false
  ; periodicBToWholeSpaceATransferConstructed = false
  ; wholeSpaceAToPeriodicBTransferConstructed = false
  ; periodicBProofProgressDoesNotPromoteWholeSpaceA = true
  ; wholeSpaceAProofProgressDoesNotPromotePeriodicB = true
  ; forcedCDDoesNotSettleUnforcedAB = true
  ; gramP3AttemptRetainedAsHistoricalProvenance = true
  ; gramP3AttemptAbandonedAsPrimaryRoute = true
  ; gramP3AbandonmentReason =
      "The partner-first/same-output Gram route, PSD compressed-difference carrier, complete-graph/P3 separation attempt, and R214 constant-band no-go are retained append-only. The route was abandoned as the primary producer after the exact amplitude telescope exposed a many-to-one observable map: incidence geometry alone cannot force separation when distinct same-output incidences can carry equal velocity arguments and therefore equal compressed slot kernels. This is a route-selection result, not a deletion or refutation of the theorem-bearing Gram infrastructure."
  }

laneAIsWholeSpace : laneA canonicalNSFourLaneProofProgram ≡ Four.A-euclidean-unforced-global
laneAIsWholeSpace = refl

laneBIsPeriodic : laneB canonicalNSFourLaneProofProgram ≡ Four.B-periodic-unforced-global
laneBIsPeriodic = refl

laneCIsForcedWholeSpace : laneC canonicalNSFourLaneProofProgram ≡ Four.C-euclidean-forced-breakdown
laneCIsForcedWholeSpace = refl

laneDIsForcedPeriodic : laneD canonicalNSFourLaneProofProgram ≡ Four.D-periodic-forced-breakdown
laneDIsForcedPeriodic = refl

statusAIsCanonical : statusA canonicalNSFourLaneProofProgram ≡ Four.statusA4
statusAIsCanonical = refl

statusBIsCanonical : statusB canonicalNSFourLaneProofProgram ≡ Four.statusB4
statusBIsCanonical = refl

statusCIsCanonical : statusC canonicalNSFourLaneProofProgram ≡ Four.statusC4
statusCIsCanonical = refl

statusDIsCanonical : statusD canonicalNSFourLaneProofProgram ≡ Four.statusD4
statusDIsCanonical = refl

forcedBreakdownDoesNotPayUnforcedAlternative :
  Four.ForcedBreakdownPaysUnforcedAlternativePermission4 → ⊥
forcedBreakdownDoesNotPayUnforcedAlternative =
  Four.forcedBreakdownDoesNotPayUnforcedAlternative4

periodicBIsActiveConstructionIsTrue :
  periodicBIsActiveConstruction canonicalNSFourLaneProofProgram ≡ true
periodicBIsActiveConstructionIsTrue = refl

wholeSpaceAIsIndependentObligationIsTrue :
  wholeSpaceAIsIndependentObligation canonicalNSFourLaneProofProgram ≡ true
wholeSpaceAIsIndependentObligationIsTrue = refl

forcedCDIsVerificationAndProvenanceIsTrue :
  forcedCDIsVerificationAndProvenance canonicalNSFourLaneProofProgram ≡ true
forcedCDIsVerificationAndProvenanceIsTrue = refl

periodicBCommutatorSpineRecoveryAssumptionActiveIsTrue :
  periodicBCommutatorSpineRecoveryAssumptionActive canonicalNSFourLaneProofProgram ≡ true
periodicBCommutatorSpineRecoveryAssumptionActiveIsTrue = refl

periodicBCommutatorSpineCertificationObservedIsFalse :
  periodicBCommutatorSpineCertificationObserved canonicalNSFourLaneProofProgram ≡ false
periodicBCommutatorSpineCertificationObservedIsFalse = refl

periodicBPhaseR104CompilerRecoveredIsTrue :
  periodicBPhaseR104CompilerRecovered canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseR104CompilerRecoveredIsTrue = refl

periodicBPhaseLiteralR406RemainderWeldRecoveredIsTrue :
  periodicBPhaseLiteralR406RemainderWeldRecovered canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseLiteralR406RemainderWeldRecoveredIsTrue = refl

periodicBPhaseCriticalRadialRealizationRecoveredIsTrue :
  periodicBPhaseCriticalRadialRealizationRecovered canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseCriticalRadialRealizationRecoveredIsTrue = refl

periodicBPhaseLiteralFiniteCriticalObservableFoldRecoveredIsTrue :
  periodicBPhaseLiteralFiniteCriticalObservableFoldRecovered canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseLiteralFiniteCriticalObservableFoldRecoveredIsTrue =
  S0.literalCriticalEndpointFoldConstructedIsTrue

periodicBPhasePointwiseCriticalEnergySplitRecoveredIsTrue :
  periodicBPhasePointwiseCriticalEnergySplitRecovered canonicalNSFourLaneProofProgram ≡ true
periodicBPhasePointwiseCriticalEnergySplitRecoveredIsTrue =
  S1a.literalFiniteCriticalEnergySplitClosedIsTrue

periodicBPhaseLiteralModeListCarrierRecoveredIsTrue :
  periodicBPhaseLiteralModeListCarrierRecovered canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseLiteralModeListCarrierRecoveredIsTrue =
  ModeCarrier.literalModeListConstancyWithoutViscosityIsTrue

periodicBPhaseCriticalEnergyCompilerGivenCalculusRecoveredIsTrue :
  periodicBPhaseCriticalEnergyCompilerGivenCalculusRecovered canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseCriticalEnergyCompilerGivenCalculusRecoveredIsTrue =
  S1b.integratedCriticalEnergyCompilerClosedGivenCalculusIsTrue

periodicBPhaseConcreteScalarFTCObservedIsFalse :
  periodicBPhaseConcreteScalarFTCObserved canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseConcreteScalarFTCObservedIsFalse =
  S1b.concreteScalarFTCInstalledIsFalse

periodicBPhaseConcreteIntegrationLinearityObservedIsFalse :
  periodicBPhaseConcreteIntegrationLinearityObserved canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseConcreteIntegrationLinearityObservedIsFalse =
  S1b.concreteIntegrationLinearityInstalledIsFalse

periodicBPhaseR414ProductionNormalisationRecoveredIsFalse :
  periodicBPhaseR414ProductionNormalisationRecovered canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseR414ProductionNormalisationRecoveredIsFalse =
  S0.r414ProductionNormalisationRecoveredIsFalse

periodicBPhasePhysicalCriticalObservableRealizationRecoveredIsFalse :
  periodicBPhasePhysicalCriticalObservableRealizationRecovered canonicalNSFourLaneProofProgram ≡ false
periodicBPhasePhysicalCriticalObservableRealizationRecoveredIsFalse = refl

periodicBPhaseCriticalEnergyInequalityRecoveredIsFalse :
  periodicBPhaseCriticalEnergyInequalityRecovered canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseCriticalEnergyInequalityRecoveredIsFalse = refl

periodicBPhaseSignedProductionEstimateRecoveredIsFalse :
  periodicBPhaseSignedProductionEstimateRecovered canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseSignedProductionEstimateRecoveredIsFalse = refl

periodicBPhaseUniformInitialCriticalCeilingRecoveredIsFalse :
  periodicBPhaseUniformInitialCriticalCeilingRecovered canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseUniformInitialCriticalCeilingRecoveredIsFalse = refl

periodicBPhasePositiveRetainedViscosityRecoveredIsFalse :
  periodicBPhasePositiveRetainedViscosityRecovered canonicalNSFourLaneProofProgram ≡ false
periodicBPhasePositiveRetainedViscosityRecoveredIsFalse = refl

periodicBPhasePhysicalR104RecoveredIsFalse :
  periodicBPhasePhysicalR104Recovered canonicalNSFourLaneProofProgram ≡ false
periodicBPhasePhysicalR104RecoveredIsFalse = refl

periodicBOnlyPhaseDiscoveryRemainsUnderCommRecoveryAssumptionIsTrue :
  periodicBOnlyPhaseDiscoveryRemainsUnderCommRecoveryAssumption canonicalNSFourLaneProofProgram ≡ true
periodicBOnlyPhaseDiscoveryRemainsUnderCommRecoveryAssumptionIsTrue = refl

wholeSpaceADeferredUntilPeriodicPortabilityAuditIsTrue :
  wholeSpaceADeferredUntilPeriodicPortabilityAudit canonicalNSFourLaneProofProgram ≡ true
wholeSpaceADeferredUntilPeriodicPortabilityAuditIsTrue = refl

periodicBToWholeSpaceATransferConstructedIsFalse :
  periodicBToWholeSpaceATransferConstructed canonicalNSFourLaneProofProgram ≡ false
periodicBToWholeSpaceATransferConstructedIsFalse = refl

wholeSpaceAToPeriodicBTransferConstructedIsFalse :
  wholeSpaceAToPeriodicBTransferConstructed canonicalNSFourLaneProofProgram ≡ false
wholeSpaceAToPeriodicBTransferConstructedIsFalse = refl

periodicBProofProgressDoesNotPromoteWholeSpaceAIsTrue :
  periodicBProofProgressDoesNotPromoteWholeSpaceA canonicalNSFourLaneProofProgram ≡ true
periodicBProofProgressDoesNotPromoteWholeSpaceAIsTrue = refl

wholeSpaceAProofProgressDoesNotPromotePeriodicBIsTrue :
  wholeSpaceAProofProgressDoesNotPromotePeriodicB canonicalNSFourLaneProofProgram ≡ true
wholeSpaceAProofProgressDoesNotPromotePeriodicBIsTrue = refl

forcedCDDoesNotSettleUnforcedABIsTrue :
  forcedCDDoesNotSettleUnforcedAB canonicalNSFourLaneProofProgram ≡ true
forcedCDDoesNotSettleUnforcedABIsTrue = refl

gramP3AttemptRetainedAsHistoricalProvenanceIsTrue :
  gramP3AttemptRetainedAsHistoricalProvenance canonicalNSFourLaneProofProgram ≡ true
gramP3AttemptRetainedAsHistoricalProvenanceIsTrue = refl

gramP3AttemptAbandonedAsPrimaryRouteIsTrue :
  gramP3AttemptAbandonedAsPrimaryRoute canonicalNSFourLaneProofProgram ≡ true
gramP3AttemptAbandonedAsPrimaryRouteIsTrue = refl

periodicBR571TaylorRealizationClosedIsFalse :
  periodicBR571TaylorRealizationClosed canonicalNSFourLaneProofProgram ≡ false
periodicBR571TaylorRealizationClosedIsFalse = refl

periodicBSecondMomentSixThreeTransplantClosedIsFalse :
  periodicBSecondMomentSixThreeTransplantClosed canonicalNSFourLaneProofProgram ≡ false
periodicBSecondMomentSixThreeTransplantClosedIsFalse = refl

periodicBR568PaymentClosedIsFalse :
  periodicBR568PaymentClosed canonicalNSFourLaneProofProgram ≡ false
periodicBR568PaymentClosedIsFalse = refl

wholeSpaceACurrentTerminalCutFrozenIsFalse :
  wholeSpaceACurrentTerminalCutFrozen canonicalNSFourLaneProofProgram ≡ false
wholeSpaceACurrentTerminalCutFrozenIsFalse = refl

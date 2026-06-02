module DASHI.Physics.Closure.NSToEV5ForwardSimulationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
import Data.Vec.Base as Vec

import DASHI.Combinatorics.FractranCOL as FractranCOL
import DASHI.Physics.Closure.NSToEV5DashiCFDExperimentPlanReceipt as Plan
import DASHI.Physics.Closure.NSToEV5ProjectionFrontierReceipt as Frontier
import DASHI.Physics.Closure.NSViscousTailDominanceReceipt as Viscous
import DASHI.Physics.Closure.TailEnergyFunctional as Tail

------------------------------------------------------------------------
-- NS -> EV5 forward simulation receipt.
--
-- This is a conservative receipt for the finite/candidate bookkeeping
-- surface.  It supplies an explicit encoding from NS shell diagnostics to
-- the five EV5 lanes and records the intended conditional shadow statement:
-- under a dissipation-dominated tail condition, the EV5 candidate may track a
-- finite NS shell shadow.  It does not prove the NS flow projects into EV5,
-- does not prove a turbulent cascade theorem, and does not promote any Clay
-- Navier-Stokes claim.

data NSToEV5ForwardSimulationStatus : Set where
  candidateFiniteBookkeeping_conditionalShadow_noForwardSimulationProof :
    NSToEV5ForwardSimulationStatus

data EncodeSurfaceComponent : Set where
  finiteShellWindowFromNSData :
    EncodeSurfaceComponent

  candidateValuationsInEV5 :
    EncodeSurfaceComponent

  v2ShellDepthBookkeeping :
    EncodeSurfaceComponent

  v3DiagnosticFluxBookkeepingOnly :
    EncodeSurfaceComponent

  v5StretchingHelicityProxyBookkeeping :
    EncodeSurfaceComponent

  v7EnstrophyTailBookkeeping :
    EncodeSurfaceComponent

  v11PhasePolarisationBookkeeping :
    EncodeSurfaceComponent

canonicalEncodeSurfaceComponents :
  List EncodeSurfaceComponent
canonicalEncodeSurfaceComponents =
  finiteShellWindowFromNSData
  ∷ candidateValuationsInEV5
  ∷ v2ShellDepthBookkeeping
  ∷ v3DiagnosticFluxBookkeepingOnly
  ∷ v5StretchingHelicityProxyBookkeeping
  ∷ v7EnstrophyTailBookkeeping
  ∷ v11PhasePolarisationBookkeeping
  ∷ []

data ConditionalShadowComponent : Set where
  assumesDissipationDominatedTail :
    ConditionalShadowComponent

  usesTailEnergyFunctionalAsFiniteRank :
    ConditionalShadowComponent

  usesViscousTailDominanceAsConditionalCutoff :
    ConditionalShadowComponent

  excludesFullTurbulentCascadeProof :
    ConditionalShadowComponent

  excludesContinuumRegularityPromotion :
    ConditionalShadowComponent

canonicalConditionalShadowComponents :
  List ConditionalShadowComponent
canonicalConditionalShadowComponents =
  assumesDissipationDominatedTail
  ∷ usesTailEnergyFunctionalAsFiniteRank
  ∷ usesViscousTailDominanceAsConditionalCutoff
  ∷ excludesFullTurbulentCascadeProof
  ∷ excludesContinuumRegularityPromotion
  ∷ []

data EmpiricalTraceStatus : Set where
  correctedTracesCanSupportCandidateOnly :
    EmpiricalTraceStatus

  correctedTracesDoNotPromoteTheorem :
    EmpiricalTraceStatus

  tracesRemainFalsificationEvidence :
    EmpiricalTraceStatus

canonicalEmpiricalTraceStatuses :
  List EmpiricalTraceStatus
canonicalEmpiricalTraceStatuses =
  correctedTracesCanSupportCandidateOnly
  ∷ correctedTracesDoNotPromoteTheorem
  ∷ tracesRemainFalsificationEvidence
  ∷ []

data PromotionStatus : Set where
  notPromoted_candidateReceiptOnly :
    PromotionStatus

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

record NSShellDataCandidate : Set where
  field
    dyadicShellDepth :
      Nat

    diagnosticCascadeFlux :
      Nat

    stretchingHelicityProxy :
      Nat

    enstrophyTailState :
      Nat

    phasePolarisationMetadata :
      Nat

open NSShellDataCandidate public

encodeNSCandidateToEV5 :
  NSShellDataCandidate →
  FractranCOL.EV5
encodeNSCandidateToEV5 c =
  Vec._∷_
    (dyadicShellDepth c)
    (Vec._∷_
      (diagnosticCascadeFlux c)
      (Vec._∷_
        (stretchingHelicityProxy c)
        (Vec._∷_
          (enstrophyTailState c)
          (Vec._∷_
            (phasePolarisationMetadata c)
            Vec.[]))))

encodedV2TracksShellDepth :
  ∀ c →
  FractranCOL.get (encodeNSCandidateToEV5 c) 0
  ≡
  dyadicShellDepth c
encodedV2TracksShellDepth c =
  refl

encodedV3TracksDiagnosticFlux :
  ∀ c →
  FractranCOL.get (encodeNSCandidateToEV5 c) 1
  ≡
  diagnosticCascadeFlux c
encodedV3TracksDiagnosticFlux c =
  refl

encodedV5TracksStretchingHelicityProxy :
  ∀ c →
  FractranCOL.get (encodeNSCandidateToEV5 c) 2
  ≡
  stretchingHelicityProxy c
encodedV5TracksStretchingHelicityProxy c =
  refl

encodedV7TracksEnstrophyTail :
  ∀ c →
  FractranCOL.get (encodeNSCandidateToEV5 c) 3
  ≡
  enstrophyTailState c
encodedV7TracksEnstrophyTail c =
  refl

encodedV11TracksPhasePolarisation :
  ∀ c →
  FractranCOL.get (encodeNSCandidateToEV5 c) 4
  ≡
  phasePolarisationMetadata c
encodedV11TracksPhasePolarisation c =
  refl

encodeSurfaceStatement :
  String
encodeSurfaceStatement =
  "Finite/candidate encode surface: NS shell diagnostics are booked into EV5 as v2=dyadic shell depth, v3=diagnostic cascade flux only, v5=stretching/helicity proxy, v7=enstrophy tail state, and v11=phase/polarisation metadata."

conditionalShadowStatement :
  String
conditionalShadowStatement =
  "Conditional shadow only: if the NS tail is dissipation-dominated at the finite cutoff, the encoded EV5 state may track the candidate finite shell shadow; this is not a proof of a full turbulent cascade or continuum regularity."

traceStatusStatement :
  String
traceStatusStatement =
  "Corrected empirical traces may support or falsify the EV5 candidate bookkeeping, but trace correction does not promote the candidate to a theorem."

promotionBoundaryStatement :
  String
promotionBoundaryStatement =
  "Promotion boundary: forward simulation, quotient correctness, Lyapunov preservation, ultrametric preservation, global smooth regularity, and Clay Navier-Stokes promotion remain false/open here."

record NSToEV5ForwardSimulationReceipt (m k : Nat) : Set₁ where
  field
    status :
      NSToEV5ForwardSimulationStatus

    statusIsCandidateOnly :
      status
      ≡
      candidateFiniteBookkeeping_conditionalShadow_noForwardSimulationProof

    encoder :
      NSShellDataCandidate → FractranCOL.EV5

    encoderIsCanonical :
      encoder ≡ encodeNSCandidateToEV5

    encodeSurfaceComponents :
      List EncodeSurfaceComponent

    encodeSurfaceComponentsAreCanonical :
      encodeSurfaceComponents ≡ canonicalEncodeSurfaceComponents

    frontierReceipt :
      Frontier.NSToEV5ProjectionFrontierReceipt

    frontierCarrierShapeClosed :
      Frontier.carrierSideEV5FractranCOLShapeClosed frontierReceipt ≡ true

    frontierForwardSimulationOpen :
      Frontier.forwardSimulationProvedHere frontierReceipt ≡ false

    frontierProjectionTheoremOpen :
      Frontier.nsProjectionTheoremProvedHere frontierReceipt ≡ false

    frontierClayPromotionFalse :
      Frontier.clayNavierStokesPromoted frontierReceipt ≡ false

    dashiCFDExperimentPlan :
      Plan.NSToEV5DashiCFDExperimentPlanReceipt

    experimentEvidenceOnly :
      Plan.evidenceOnly dashiCFDExperimentPlan ≡ true

    experimentProjectionNotProved :
      Plan.nsToEV5ProjectionProvedHere dashiCFDExperimentPlan ≡ false

    experimentClayPromotionFalse :
      Plan.clayNavierStokesPromoted dashiCFDExperimentPlan ≡ false

    viscousTailReceipt :
      Viscous.NSViscousTailDominanceReceipt

    viscousTailKolmogorovOnly :
      Viscous.kolmogorovCalibratedOnly viscousTailReceipt ≡ true

    viscousTailUniversalNSFalse :
      Viscous.universalNSRegularityTheorem viscousTailReceipt ≡ false

    viscousTailClayPromotionFalse :
      Viscous.clayNavierStokesPromoted viscousTailReceipt ≡ false

    tailEnergyFunctional :
      Tail.TailEnergyFunctional m k

    tailEnergyFunctionalIsCanonical :
      tailEnergyFunctional ≡ Tail.canonicalTailEnergyFunctional m k

    conditionalShadowComponents :
      List ConditionalShadowComponent

    conditionalShadowComponentsAreCanonical :
      conditionalShadowComponents ≡ canonicalConditionalShadowComponents

    dissipationDominatedConditionRequired :
      Bool

    dissipationDominatedConditionRequiredIsTrue :
      dissipationDominatedConditionRequired ≡ true

    finiteCandidateShadowRecorded :
      Bool

    finiteCandidateShadowRecordedIsTrue :
      finiteCandidateShadowRecorded ≡ true

    fullTurbulentCascadeProof :
      Bool

    fullTurbulentCascadeProofIsFalse :
      fullTurbulentCascadeProof ≡ false

    forwardSimulationTheoremProved :
      Bool

    forwardSimulationTheoremProvedIsFalse :
      forwardSimulationTheoremProved ≡ false

    quotientCorrectnessProved :
      Bool

    quotientCorrectnessProvedIsFalse :
      quotientCorrectnessProved ≡ false

    lyapunovPreservationProved :
      Bool

    lyapunovPreservationProvedIsFalse :
      lyapunovPreservationProved ≡ false

    ultrametricPreservationProved :
      Bool

    ultrametricPreservationProvedIsFalse :
      ultrametricPreservationProved ≡ false

    correctedEmpiricalTraceStatuses :
      List EmpiricalTraceStatus

    correctedEmpiricalTraceStatusesAreCanonical :
      correctedEmpiricalTraceStatuses ≡ canonicalEmpiricalTraceStatuses

    correctedTracesSupportCandidate :
      Bool

    correctedTracesSupportCandidateIsTrue :
      correctedTracesSupportCandidate ≡ true

    correctedTracesPromoteTheorem :
      Bool

    correctedTracesPromoteTheoremIsFalse :
      correctedTracesPromoteTheorem ≡ false

    promotionStatus :
      PromotionStatus

    promotionStatusIsNotPromoted :
      promotionStatus ≡ notPromoted_candidateReceiptOnly

    generalClayPromotion :
      Bool

    generalClayPromotionIsFalse :
      generalClayPromotion ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    encodeSurfaceSummary :
      String

    encodeSurfaceSummaryIsCanonical :
      encodeSurfaceSummary ≡ encodeSurfaceStatement

    conditionalShadowSummary :
      String

    conditionalShadowSummaryIsCanonical :
      conditionalShadowSummary ≡ conditionalShadowStatement

    traceStatusSummary :
      String

    traceStatusSummaryIsCanonical :
      traceStatusSummary ≡ traceStatusStatement

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionBoundaryStatement

open NSToEV5ForwardSimulationReceipt public

canonicalNSToEV5ForwardSimulationReceipt :
  ∀ (m k : Nat) →
  NSToEV5ForwardSimulationReceipt m k
canonicalNSToEV5ForwardSimulationReceipt m k =
  record
    { status =
        candidateFiniteBookkeeping_conditionalShadow_noForwardSimulationProof
    ; statusIsCandidateOnly =
        refl
    ; encoder =
        encodeNSCandidateToEV5
    ; encoderIsCanonical =
        refl
    ; encodeSurfaceComponents =
        canonicalEncodeSurfaceComponents
    ; encodeSurfaceComponentsAreCanonical =
        refl
    ; frontierReceipt =
        Frontier.canonicalNSToEV5ProjectionFrontierReceipt
    ; frontierCarrierShapeClosed =
        refl
    ; frontierForwardSimulationOpen =
        refl
    ; frontierProjectionTheoremOpen =
        refl
    ; frontierClayPromotionFalse =
        refl
    ; dashiCFDExperimentPlan =
        Plan.canonicalNSToEV5DashiCFDExperimentPlanReceipt
    ; experimentEvidenceOnly =
        refl
    ; experimentProjectionNotProved =
        refl
    ; experimentClayPromotionFalse =
        refl
    ; viscousTailReceipt =
        Viscous.canonicalNSViscousTailDominanceReceipt
    ; viscousTailKolmogorovOnly =
        refl
    ; viscousTailUniversalNSFalse =
        refl
    ; viscousTailClayPromotionFalse =
        refl
    ; tailEnergyFunctional =
        Tail.canonicalTailEnergyFunctional m k
    ; tailEnergyFunctionalIsCanonical =
        refl
    ; conditionalShadowComponents =
        canonicalConditionalShadowComponents
    ; conditionalShadowComponentsAreCanonical =
        refl
    ; dissipationDominatedConditionRequired =
        true
    ; dissipationDominatedConditionRequiredIsTrue =
        refl
    ; finiteCandidateShadowRecorded =
        true
    ; finiteCandidateShadowRecordedIsTrue =
        refl
    ; fullTurbulentCascadeProof =
        false
    ; fullTurbulentCascadeProofIsFalse =
        refl
    ; forwardSimulationTheoremProved =
        false
    ; forwardSimulationTheoremProvedIsFalse =
        refl
    ; quotientCorrectnessProved =
        false
    ; quotientCorrectnessProvedIsFalse =
        refl
    ; lyapunovPreservationProved =
        false
    ; lyapunovPreservationProvedIsFalse =
        refl
    ; ultrametricPreservationProved =
        false
    ; ultrametricPreservationProvedIsFalse =
        refl
    ; correctedEmpiricalTraceStatuses =
        canonicalEmpiricalTraceStatuses
    ; correctedEmpiricalTraceStatusesAreCanonical =
        refl
    ; correctedTracesSupportCandidate =
        true
    ; correctedTracesSupportCandidateIsTrue =
        refl
    ; correctedTracesPromoteTheorem =
        false
    ; correctedTracesPromoteTheoremIsFalse =
        refl
    ; promotionStatus =
        notPromoted_candidateReceiptOnly
    ; promotionStatusIsNotPromoted =
        refl
    ; generalClayPromotion =
        false
    ; generalClayPromotionIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; encodeSurfaceSummary =
        encodeSurfaceStatement
    ; encodeSurfaceSummaryIsCanonical =
        refl
    ; conditionalShadowSummary =
        conditionalShadowStatement
    ; conditionalShadowSummaryIsCanonical =
        refl
    ; traceStatusSummary =
        traceStatusStatement
    ; traceStatusSummaryIsCanonical =
        refl
    ; promotionBoundary =
        promotionBoundaryStatement
    ; promotionBoundaryIsCanonical =
        refl
    }

nsToEV5ForwardSimulationRemainsCandidateOnly :
  ∀ (m k : Nat) →
  forwardSimulationTheoremProved
    (canonicalNSToEV5ForwardSimulationReceipt m k)
  ≡
  false
nsToEV5ForwardSimulationRemainsCandidateOnly m k =
  refl

nsToEV5CorrectedTracesDoNotPromoteTheorem :
  ∀ (m k : Nat) →
  correctedTracesPromoteTheorem
    (canonicalNSToEV5ForwardSimulationReceipt m k)
  ≡
  false
nsToEV5CorrectedTracesDoNotPromoteTheorem m k =
  refl

nsToEV5GeneralClayPromotionFalse :
  ∀ (m k : Nat) →
  generalClayPromotion
    (canonicalNSToEV5ForwardSimulationReceipt m k)
  ≡
  false
nsToEV5GeneralClayPromotionFalse m k =
  refl

nsToEV5PromotionStatusNotPromoted :
  ∀ (m k : Nat) →
  promotionStatus
    (canonicalNSToEV5ForwardSimulationReceipt m k)
  ≡
  notPromoted_candidateReceiptOnly
nsToEV5PromotionStatusNotPromoted m k =
  refl

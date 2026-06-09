module DASHI.Physics.Closure.NSToEV5ForwardSimulationActualReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
import Data.Vec.Base as Vec

import DASHI.Combinatorics.FractranCOL as FractranCOL
import DASHI.Physics.Closure.DashiCFDThetaRuntimeDiagnosticReceipt as Runtime
import DASHI.Physics.Closure.EV5ThetaMarginUpgradeReceipt as EV5Theta
import DASHI.Physics.Closure.NSThetaImpliesTailDecayReceipt as TailDecay
import DASHI.Physics.Closure.NSToEV5ForwardSimulationReceipt as Prior

------------------------------------------------------------------------
-- Actual NS-to-EV5 projection surface for the theta-controlled lane.
--
-- The projection records the Manager-B lane assignment:
--   lane2 = danger shell index,
--   lane7 = tail energy,
--   lane3/v3 = diagnostic flux sign/proxy only,
--   lane5/lane11 = metadata slots retained for compatibility.
-- The forward simulation is exact only up to an explicitly named LP
-- commutator defect; making that defect vanish requires Serrin/BKM control.

record NSThetaProjectionState : Set where
  field
    dangerShellK :
      Nat

    tailEnergyLane7 :
      Nat

    diagnosticFluxV3 :
      Nat

    stretchingProxyV5 :
      Nat

    phaseMetadataV11 :
      Nat

open NSThetaProjectionState public

encodeActualNSProjection :
  NSThetaProjectionState →
  FractranCOL.EV5
encodeActualNSProjection s =
  Vec._∷_
    (dangerShellK s)
    (Vec._∷_
      (diagnosticFluxV3 s)
      (Vec._∷_
        (stretchingProxyV5 s)
        (Vec._∷_
          (tailEnergyLane7 s)
          (Vec._∷_
            (phaseMetadataV11 s)
            Vec.[]))))

encodedLane2TracksDangerShell :
  (s : NSThetaProjectionState) →
  FractranCOL.get (encodeActualNSProjection s) 0
  ≡
  dangerShellK s
encodedLane2TracksDangerShell s =
  refl

encodedLane7TracksTailEnergy :
  (s : NSThetaProjectionState) →
  FractranCOL.get (encodeActualNSProjection s) 3
  ≡
  tailEnergyLane7 s
encodedLane7TracksTailEnergy s =
  refl

data ForwardSimulationDefect : Set where
  lpCommutatorDefect :
    ForwardSimulationDefect

data ForwardSimulationDefectBound : Set where
  defectBoundedByTwoToMinusKStarTimesHsNorm :
    ForwardSimulationDefectBound

data ForwardSimulationConclusion : Set where
  ev5StepShadowsNSStepUpToControlledDefect :
    ForwardSimulationConclusion

data ExactForwardSimulationCondition : Set where
  defectVanishesUnderSerrinOrBKMControl :
    ExactForwardSimulationCondition

forwardSimulationUpToDefect :
  ForwardSimulationDefectBound →
  ForwardSimulationConclusion
forwardSimulationUpToDefect defectBoundedByTwoToMinusKStarTimesHsNorm =
  ev5StepShadowsNSStepUpToControlledDefect

data NSToEV5ActualProjectionComponent : Set where
  lane2IsDangerShellIndex :
    NSToEV5ActualProjectionComponent

  lane7IsTailEnergyAtDangerShell :
    NSToEV5ActualProjectionComponent

  v3ExcludedFromLyapunovAndKeptDiagnosticOnly :
    NSToEV5ActualProjectionComponent

  ev5StepSubtractsThetaControlledDissipation :
    NSToEV5ActualProjectionComponent

  forwardSimulationHasCommutatorDefect :
    NSToEV5ActualProjectionComponent

  exactShadowRequiresSerrinOrBKM :
    NSToEV5ActualProjectionComponent

canonicalNSToEV5ActualProjectionComponents :
  List NSToEV5ActualProjectionComponent
canonicalNSToEV5ActualProjectionComponents =
  lane2IsDangerShellIndex
  ∷ lane7IsTailEnergyAtDangerShell
  ∷ v3ExcludedFromLyapunovAndKeptDiagnosticOnly
  ∷ ev5StepSubtractsThetaControlledDissipation
  ∷ forwardSimulationHasCommutatorDefect
  ∷ exactShadowRequiresSerrinOrBKM
  ∷ []

data NSToEV5ActualPromotion : Set where

nsToEV5ActualPromotionImpossibleHere :
  NSToEV5ActualPromotion →
  ⊥
nsToEV5ActualPromotionImpossibleHere ()

projectionFormula :
  String
projectionFormula =
  "encode(u): lane2=K*(u), lane7=E_{>K*}(u), v3=diagnostic flux only, with EV5 shadow exact only up to an LP commutator defect."

defectFormula :
  String
defectFormula =
  "delta <= C 2^{-K*} ||u||_{H^s}^2 is the recorded defect shape; delta=0 requires Serrin/BKM-type control."

canonicalProjectionState :
  NSThetaProjectionState
canonicalProjectionState =
  record
    { dangerShellK =
        zero
    ; tailEnergyLane7 =
        zero
    ; diagnosticFluxV3 =
        zero
    ; stretchingProxyV5 =
        zero
    ; phaseMetadataV11 =
        zero
    }

record NSToEV5ForwardSimulationActualReceipt : Setω where
  field
    priorForwardSimulationReceipt :
      Prior.NSToEV5ForwardSimulationReceipt zero zero

    priorForwardSimulationRemainsCandidate :
      Prior.clayNavierStokesPromoted priorForwardSimulationReceipt ≡ false

    thetaTailDecayReceipt :
      TailDecay.NSThetaImpliesTailDecayReceipt zero

    thetaTailDecayNoClay :
      TailDecay.clayNavierStokesPromoted thetaTailDecayReceipt ≡ false

    runtimeDiagnosticReceipt :
      Runtime.DashiCFDThetaRuntimeDiagnosticReceipt

    runtimeDiagnosticNoClay :
      Runtime.clayNavierStokesPromoted runtimeDiagnosticReceipt ≡ false

    sampleState :
      NSThetaProjectionState

    sampleStateIsCanonical :
      sampleState ≡ canonicalProjectionState

    encoder :
      NSThetaProjectionState → FractranCOL.EV5

    encoderIsActualProjection :
      encoder ≡ encodeActualNSProjection

    lane2TracksDangerShell :
      FractranCOL.get (encoder sampleState) 0
      ≡
      dangerShellK sampleState

    lane7TracksTailEnergy :
      FractranCOL.get (encoder sampleState) 3
      ≡
      tailEnergyLane7 sampleState

    components :
      List NSToEV5ActualProjectionComponent

    componentsAreCanonical :
      components ≡ canonicalNSToEV5ActualProjectionComponents

    defect :
      ForwardSimulationDefect

    defectIsLPCommutator :
      defect ≡ lpCommutatorDefect

    defectBound :
      ForwardSimulationDefectBound

    forwardSimulationConclusion :
      ForwardSimulationConclusion

    forwardSimulationConclusionIsFromDefectBound :
      forwardSimulationConclusion ≡ forwardSimulationUpToDefect defectBound

    exactForwardSimulationCondition :
      ExactForwardSimulationCondition

    projectionStatement :
      String

    projectionStatementIsCanonical :
      projectionStatement ≡ projectionFormula

    defectStatement :
      String

    defectStatementIsCanonical :
      defectStatement ≡ defectFormula

    nsToEV5SimulationDefined :
      Bool

    nsToEV5SimulationDefinedIsTrue :
      nsToEV5SimulationDefined ≡ true

    forwardSimulationDefectBounded :
      Bool

    forwardSimulationDefectBoundedIsTrue :
      forwardSimulationDefectBounded ≡ true

    defectZeroRequiresSerrin :
      Bool

    defectZeroRequiresSerrinIsTrue :
      defectZeroRequiresSerrin ≡ true

    exactForwardSimulationProvedHere :
      Bool

    exactForwardSimulationProvedHereIsFalse :
      exactForwardSimulationProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSToEV5ActualPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSToEV5ActualPromotion →
      ⊥

open NSToEV5ForwardSimulationActualReceipt public

canonicalNSToEV5ForwardSimulationActualReceipt :
  NSToEV5ForwardSimulationActualReceipt
canonicalNSToEV5ForwardSimulationActualReceipt =
  record
    { priorForwardSimulationReceipt =
        Prior.canonicalNSToEV5ForwardSimulationReceipt zero zero
    ; priorForwardSimulationRemainsCandidate =
        refl
    ; thetaTailDecayReceipt =
        TailDecay.canonicalNSThetaImpliesTailDecayReceipt
    ; thetaTailDecayNoClay =
        refl
    ; runtimeDiagnosticReceipt =
        Runtime.canonicalDashiCFDThetaRuntimeDiagnosticReceipt
    ; runtimeDiagnosticNoClay =
        refl
    ; sampleState =
        canonicalProjectionState
    ; sampleStateIsCanonical =
        refl
    ; encoder =
        encodeActualNSProjection
    ; encoderIsActualProjection =
        refl
    ; lane2TracksDangerShell =
        refl
    ; lane7TracksTailEnergy =
        refl
    ; components =
        canonicalNSToEV5ActualProjectionComponents
    ; componentsAreCanonical =
        refl
    ; defect =
        lpCommutatorDefect
    ; defectIsLPCommutator =
        refl
    ; defectBound =
        defectBoundedByTwoToMinusKStarTimesHsNorm
    ; forwardSimulationConclusion =
        ev5StepShadowsNSStepUpToControlledDefect
    ; forwardSimulationConclusionIsFromDefectBound =
        refl
    ; exactForwardSimulationCondition =
        defectVanishesUnderSerrinOrBKMControl
    ; projectionStatement =
        projectionFormula
    ; projectionStatementIsCanonical =
        refl
    ; defectStatement =
        defectFormula
    ; defectStatementIsCanonical =
        refl
    ; nsToEV5SimulationDefined =
        true
    ; nsToEV5SimulationDefinedIsTrue =
        refl
    ; forwardSimulationDefectBounded =
        true
    ; forwardSimulationDefectBoundedIsTrue =
        refl
    ; defectZeroRequiresSerrin =
        true
    ; defectZeroRequiresSerrinIsTrue =
        refl
    ; exactForwardSimulationProvedHere =
        false
    ; exactForwardSimulationProvedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsToEV5ActualPromotionImpossibleHere
    }

canonicalNSToEV5ActualNoClayPromotion :
  clayNavierStokesPromoted canonicalNSToEV5ForwardSimulationActualReceipt
  ≡ false
canonicalNSToEV5ActualNoClayPromotion =
  refl

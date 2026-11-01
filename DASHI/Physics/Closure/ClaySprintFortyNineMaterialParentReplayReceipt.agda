module DASHI.Physics.Closure.ClaySprintFortyNineMaterialParentReplayReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintFortyEightReplenishmentDecompositionReceipt
  as Sprint48

------------------------------------------------------------------------
-- Sprint 49 material-parent replay.
--
-- dashiCFD owns the heavy GPU material-parent matching.  This dashi_agda
-- receipt records only the lightweight replay boundary for the GPU-produced
-- material parent summary.  It never reruns the N64 shell/packet diagnostics
-- on CPU and it cannot promote Clay regularity.

Shell : Set
Shell = Nat

Scalar : Set
Scalar = String

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

data MaterialParentSource : Set where
  trueNew :
    MaterialParentSource
  trackingUncertain :
    MaterialParentSource
  crossShell :
    MaterialParentSource
  lowShellInjection :
    MaterialParentSource
  totalMaterial :
    MaterialParentSource

canonicalMaterialParentSources :
  List MaterialParentSource
canonicalMaterialParentSources =
  trueNew
  ∷ trackingUncertain
  ∷ crossShell
  ∷ lowShellInjection
  ∷ totalMaterial
  ∷ []

data MaterialParentExponent : Set where
  sigmaTrueNew :
    MaterialParentExponent
  sigmaTrackingUncertain :
    MaterialParentExponent
  sigmaCrossShell :
    MaterialParentExponent
  sigmaLowShell :
    MaterialParentExponent
  sigmaTotalMaterial :
    MaterialParentExponent

canonicalMaterialParentExponents :
  List MaterialParentExponent
canonicalMaterialParentExponents =
  sigmaTrueNew
  ∷ sigmaTrackingUncertain
  ∷ sigmaCrossShell
  ∷ sigmaLowShell
  ∷ sigmaTotalMaterial
  ∷ []

data Sprint49OpenGate : Set where
  gateGPUParentContract :
    Sprint49OpenGate
  gateTrueNewSourceSummable :
    Sprint49OpenGate
  gateTrackingUncertaintyResolved :
    Sprint49OpenGate
  gateAdjacentPacketTheorem :
    Sprint49OpenGate
  gateUniformPhysicalBridge :
    Sprint49OpenGate
  gateStretchAbsorption :
    Sprint49OpenGate
  gateNoFiniteTimeBlowup :
    Sprint49OpenGate

canonicalSprint49OpenGates :
  List Sprint49OpenGate
canonicalSprint49OpenGates =
  gateGPUParentContract
  ∷ gateTrueNewSourceSummable
  ∷ gateTrackingUncertaintyResolved
  ∷ gateAdjacentPacketTheorem
  ∷ gateUniformPhysicalBridge
  ∷ gateStretchAbsorption
  ∷ gateNoFiniteTimeBlowup
  ∷ []

data Sprint49Promotion : Set where

sprint49PromotionImpossibleHere :
  Sprint49Promotion →
  ⊥
sprint49PromotionImpossibleHere ()

sourceCount : Nat
sourceCount = 5

exponentCount : Nat
exponentCount = 5

openGateCount : Nat
openGateCount = 7

materialParentReplayContract : String
materialParentReplayContract =
  "ns_material_parent_summary.csv/json replay source_true_new, source_tracking_uncertain, source_cross_shell, source_low_shell_injection, source_total_material, weighted components, sigma fits, and route_status"

materialParentDecisionRule : String
materialParentDecisionRule =
  "route_status separates true-new subcritical, tracking-uncertain, adjacent-packet insufficiency, and diagnostic-only repaired source cases"

sprint49Boundary : String
sprint49Boundary =
  "Sprint 49 replays GPU material-parent diagnostics only. It does not prove source summability, the physical bridge, stretch absorption, no finite-time blowup, or Clay regularity."

record ClaySprintFortyNineMaterialParentReplayReceipt : Set₁ where
  field
    sprint48NoPromotion :
      Sprint48.clayNavierStokesPromoted ≡ false

    replayConsumesGPUParentSummary :
      Bool
    replayConsumesGPUParentSummaryIsTrue :
      replayConsumesGPUParentSummary ≡ true

    replayRerunsN64ShellPacketsOnCPU :
      Bool
    replayRerunsN64ShellPacketsOnCPUIsFalse :
      replayRerunsN64ShellPacketsOnCPU ≡ false

    materialParentSources :
      List MaterialParentSource
    materialParentSourcesAreCanonical :
      materialParentSources ≡ canonicalMaterialParentSources

    materialParentExponents :
      List MaterialParentExponent
    materialParentExponentsAreCanonical :
      materialParentExponents ≡ canonicalMaterialParentExponents

    openGates :
      List Sprint49OpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint49OpenGates

    trueNewSourceValue :
      Shell → Scalar
    trackingUncertainSourceValue :
      Shell → Scalar
    crossShellSourceValue :
      Shell → Scalar
    lowShellInjectionSourceValue :
      Shell → Scalar
    totalMaterialSourceValue :
      Shell → Scalar

    outputContract :
      String
    outputContractIsCanonical :
      outputContract ≡ materialParentReplayContract

    decisionRule :
      String
    decisionRuleIsCanonical :
      decisionRule ≡ materialParentDecisionRule

    trueNewSourceSummable :
      Bool
    trueNewSourceSummableIsFalse :
      trueNewSourceSummable ≡ false

    trackingUncertaintyResolved :
      Bool
    trackingUncertaintyResolvedIsFalse :
      trackingUncertaintyResolved ≡ false

    adjacentPacketTheoremSufficient :
      Bool
    adjacentPacketTheoremSufficientIsFalse :
      adjacentPacketTheoremSufficient ≡ false

    uniformPhysicalBridge :
      Bool
    uniformPhysicalBridgeIsFalse :
      uniformPhysicalBridge ≡ false

    stretchAbsorption :
      Bool
    stretchAbsorptionIsFalse :
      stretchAbsorption ≡ false

    noFiniteTimeBlowup :
      Bool
    noFiniteTimeBlowupIsFalse :
      noFiniteTimeBlowup ≡ false

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List Sprint49Promotion
    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Sprint49Promotion →
      ⊥

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint49Boundary

open ClaySprintFortyNineMaterialParentReplayReceipt public

canonicalClaySprintFortyNineMaterialParentReplayReceipt :
  ClaySprintFortyNineMaterialParentReplayReceipt
canonicalClaySprintFortyNineMaterialParentReplayReceipt =
  record
    { sprint48NoPromotion =
        refl
    ; replayConsumesGPUParentSummary =
        true
    ; replayConsumesGPUParentSummaryIsTrue =
        refl
    ; replayRerunsN64ShellPacketsOnCPU =
        false
    ; replayRerunsN64ShellPacketsOnCPUIsFalse =
        refl
    ; materialParentSources =
        canonicalMaterialParentSources
    ; materialParentSourcesAreCanonical =
        refl
    ; materialParentExponents =
        canonicalMaterialParentExponents
    ; materialParentExponentsAreCanonical =
        refl
    ; openGates =
        canonicalSprint49OpenGates
    ; openGatesAreCanonical =
        refl
    ; trueNewSourceValue =
        λ _ → "gpu-summary-replay-only"
    ; trackingUncertainSourceValue =
        λ _ → "gpu-summary-replay-only"
    ; crossShellSourceValue =
        λ _ → "gpu-summary-replay-only"
    ; lowShellInjectionSourceValue =
        λ _ → "gpu-summary-replay-only"
    ; totalMaterialSourceValue =
        λ _ → "gpu-summary-replay-only"
    ; outputContract =
        materialParentReplayContract
    ; outputContractIsCanonical =
        refl
    ; decisionRule =
        materialParentDecisionRule
    ; decisionRuleIsCanonical =
        refl
    ; trueNewSourceSummable =
        false
    ; trueNewSourceSummableIsFalse =
        refl
    ; trackingUncertaintyResolved =
        false
    ; trackingUncertaintyResolvedIsFalse =
        refl
    ; adjacentPacketTheoremSufficient =
        false
    ; adjacentPacketTheoremSufficientIsFalse =
        refl
    ; uniformPhysicalBridge =
        false
    ; uniformPhysicalBridgeIsFalse =
        refl
    ; stretchAbsorption =
        false
    ; stretchAbsorptionIsFalse =
        refl
    ; noFiniteTimeBlowup =
        false
    ; noFiniteTimeBlowupIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        sprint49PromotionImpossibleHere
    ; boundary =
        sprint49Boundary
    ; boundaryIsCanonical =
        refl
    }

sourceCountCheck : sourceCount ≡ 5
sourceCountCheck = refl

exponentCountCheck : exponentCount ≡ 5
exponentCountCheck = refl

openGateCountCheck : openGateCount ≡ 7
openGateCountCheck = refl

canonicalSprint49NoClay :
  clayNavierStokesPromoted ≡ false
canonicalSprint49NoClay =
  refl

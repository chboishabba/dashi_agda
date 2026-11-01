module DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
import DASHI.Execution.Contract as Exec
import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
import DASHI.Physics.Closure.AlternativeCarrierSignatureStress as ACSS
import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
import DASHI.Physics.Closure.ObservableTransportGaugeEntry as OTGE
import DASHI.Physics.Closure.ShiftContractAnchoredTrajectoryFamily as SATF
import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ESA
import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF

------------------------------------------------------------------------
-- Non-singleton shift-backed observable/signature pressure-test carrier.
--
-- The previous inhabited pressure test used a singleton canonical point.  This
-- module keeps the same theorem-thin signature gate, but places it over the
-- live `shiftContract {1}{3}` carrier and exposes the anchored trajectory
-- states as pressure points.

private
  ShiftC : Exec.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

ShiftPressureState : Set
ShiftPressureState = Exec.Contract.State ShiftC

shiftPressureStart : ShiftPressureState
shiftPressureStart = SATF.trajectoryGen STF.i0

shiftPressureNext : ShiftPressureState
shiftPressureNext = SATF.trajectoryGen STF.i1

shiftPressureHeldExit : ShiftPressureState
shiftPressureHeldExit = ESA.oneHot0

shiftPressureLiveStep :
  Exec.Contract.step ShiftC shiftPressureStart ≡ shiftPressureNext
shiftPressureLiveStep = SATF.trajectoryStep01

shiftPressureExitStep :
  Exec.Contract.step ShiftC (SATF.trajectoryGen STF.i2) ≡ shiftPressureHeldExit
shiftPressureExitStep = SATF.trajectoryStep2Exit

data ShiftPressurePoint : Set where
  shiftStartPoint : ShiftPressurePoint
  shiftNextPoint : ShiftPressurePoint
  shiftHeldExitPoint : ShiftPressurePoint

shiftPointState : ShiftPressurePoint → ShiftPressureState
shiftPointState shiftStartPoint = shiftPressureStart
shiftPointState shiftNextPoint = shiftPressureNext
shiftPointState shiftHeldExitPoint = shiftPressureHeldExit

shiftObservableCarriers : OTGE.ObservableTransportCarriers
shiftObservableCarriers = record
  { ObservableCarrier = ShiftPressureState
  ; PhysicsCarrier = ShiftPressurePoint
  }

shiftObservableContract :
  OTGE.ObservableTransportContract shiftObservableCarriers
shiftObservableContract = record
  { transport = shiftPointState
  ; observableProjection = λ x → x
  ; admissible = λ _ → ⊤
  ; transportStable = λ _ _ → ⊤
  ; projectionCoherent = λ _ _ → ⊤
  }

shiftObservableGate :
  OTGE.ObservableTransportGaugeEntry shiftObservableContract
shiftObservableGate = record
  { gaugeEntryBoundary = λ _ → ⊤
  ; status = shiftObservableStatus
  ; admissibilityWitness = shiftObservableAdmissibilityWitness
  ; stabilityWitness = λ _ _ → tt
  ; coherenceWitness = λ _ _ → tt
  }
  where
    shiftObservableStatus : ShiftPressurePoint → OTGE.GaugeEntryStatus
    shiftObservableStatus shiftStartPoint = OTGE.forced
    shiftObservableStatus shiftNextPoint = OTGE.forced
    shiftObservableStatus shiftHeldExitPoint = OTGE.held

    shiftObservableAdmissibilityWitness :
      (p : ShiftPressurePoint) →
      shiftObservableStatus p ≡ OTGE.forced →
      ⊤
    shiftObservableAdmissibilityWitness shiftStartPoint _ = tt
    shiftObservableAdmissibilityWitness shiftNextPoint _ = tt
    shiftObservableAdmissibilityWitness shiftHeldExitPoint ()

shiftSignatureCarrier : ACSS.AlternativeCarrier
shiftSignatureCarrier = record
  { Carrier = ShiftPressurePoint
  ; QuadraticCarrier = ⊤
  }

shiftSignatureBridge :
  CQSB.ContractionQuadraticToSignatureBridgeTheorem
shiftSignatureBridge =
  CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem

shiftSignatureContract :
  ACSS.CarrierSignatureStressContract shiftSignatureCarrier
shiftSignatureContract = record
  { toQuadratic = λ _ → tt
  ; signatureOf = λ _ →
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
        shiftSignatureBridge
  ; carrierInvariant = λ _ → ⊤
  ; transportCompatible = λ _ _ → ⊤
  ; signatureCompatible = λ _ _ → ⊤
  ; obstruction = λ _ → ⊤
  }

shiftSignatureStress :
  ACSS.AlternativeCarrierSignatureStress shiftSignatureContract
shiftSignatureStress = record
  { status = shiftSignatureStatus
  ; stressReason = λ _ → ⊤
  ; forced31 = shiftForced31
  ; conditionalInvariant = shiftNoConditionalInvariant
  ; conditionalTransport = shiftNoConditionalTransport
  ; conditionalSignature = shiftNoConditionalSignature
  ; failedObstruction = shiftNoFailedObstruction
  }
  where
    shiftSignatureStatus : ShiftPressurePoint → ACSS.SignatureStressStatus
    shiftSignatureStatus shiftStartPoint = ACSS.forced
    shiftSignatureStatus shiftNextPoint = ACSS.forced
    shiftSignatureStatus shiftHeldExitPoint = ACSS.held

    shiftForced31 :
      (x : ShiftPressurePoint) →
      shiftSignatureStatus x ≡ ACSS.forced →
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
        shiftSignatureBridge
      ≡
      CTI.sig31
    shiftForced31 shiftStartPoint _ =
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
        shiftSignatureBridge
    shiftForced31 shiftNextPoint _ =
      CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
        shiftSignatureBridge
    shiftForced31 shiftHeldExitPoint ()

    shiftNoConditionalInvariant :
      (x : ShiftPressurePoint) →
      shiftSignatureStatus x ≡ ACSS.conditional →
      ⊤
    shiftNoConditionalInvariant shiftStartPoint ()
    shiftNoConditionalInvariant shiftNextPoint ()
    shiftNoConditionalInvariant shiftHeldExitPoint ()

    shiftNoConditionalTransport :
      (x : ShiftPressurePoint) →
      (s : shiftSignatureStatus x ≡ ACSS.conditional) →
      ⊤
    shiftNoConditionalTransport shiftStartPoint ()
    shiftNoConditionalTransport shiftNextPoint ()
    shiftNoConditionalTransport shiftHeldExitPoint ()

    shiftNoConditionalSignature :
      (x : ShiftPressurePoint) →
      (s : shiftSignatureStatus x ≡ ACSS.conditional) →
      ⊤
    shiftNoConditionalSignature shiftStartPoint ()
    shiftNoConditionalSignature shiftNextPoint ()
    shiftNoConditionalSignature shiftHeldExitPoint ()

    shiftNoFailedObstruction :
      (x : ShiftPressurePoint) →
      shiftSignatureStatus x ≡ ACSS.failed →
      ⊤
    shiftNoFailedObstruction shiftStartPoint ()
    shiftNoFailedObstruction shiftNextPoint ()
    shiftNoFailedObstruction shiftHeldExitPoint ()

shiftPressureStatus : ShiftPressurePoint → OSPT.PhysicsPressureStatus
shiftPressureStatus shiftStartPoint = OSPT.promotionReady
shiftPressureStatus shiftNextPoint = OSPT.promotionReady
shiftPressureStatus shiftHeldExitPoint = OSPT.held

shiftObservableSignaturePressureTest :
  OSPT.ObservableSignaturePressureTest
    shiftObservableContract
    shiftSignatureContract
shiftObservableSignaturePressureTest = record
  { observableGate = shiftObservableGate
  ; signatureStress = shiftSignatureStress
  ; alignState = λ x → x
  ; pressureStatus = shiftPressureStatus
  ; readyWhenForced = shiftReadyWhenForced
  ; conditionalBoundary = λ _ _ → ⊤
  ; blockedBoundary = λ _ _ → ⊤
  ; heldBoundary = λ _ _ → ⊤
  ; noGaugeMatterRecoveryClaim = tt
  }
  where
    shiftReadyWhenForced :
      (p : ShiftPressurePoint) →
      OTGE.status shiftObservableGate p ≡ OTGE.forced →
      ACSS.status shiftSignatureStress p ≡ ACSS.forced →
      shiftPressureStatus p ≡ OSPT.promotionReady
    shiftReadyWhenForced shiftStartPoint _ _ = refl
    shiftReadyWhenForced shiftNextPoint _ _ = refl
    shiftReadyWhenForced shiftHeldExitPoint ()

shiftStartObservableForced :
  OTGE.status shiftObservableGate shiftStartPoint ≡ OTGE.forced
shiftStartObservableForced = refl

shiftStartSignatureForced :
  ACSS.status shiftSignatureStress shiftStartPoint ≡ ACSS.forced
shiftStartSignatureForced = refl

shiftStartPromotionReady :
  OSPT.pressureStatus
    shiftObservableSignaturePressureTest
    shiftStartPoint
  ≡
  OSPT.promotionReady
shiftStartPromotionReady = refl

shiftStartPromotionReadyPoint :
  OSPT.PromotionReadyPressurePoint
    shiftObservableSignaturePressureTest
    shiftStartPoint
shiftStartPromotionReadyPoint =
  OSPT.promotionReadyPressurePoint
    shiftObservableSignaturePressureTest
    shiftStartPoint
    shiftStartObservableForced
    shiftStartSignatureForced

shiftNextObservableForced :
  OTGE.status shiftObservableGate shiftNextPoint ≡ OTGE.forced
shiftNextObservableForced = refl

shiftNextSignatureForced :
  ACSS.status shiftSignatureStress shiftNextPoint ≡ ACSS.forced
shiftNextSignatureForced = refl

shiftNextPromotionReadyPoint :
  OSPT.PromotionReadyPressurePoint
    shiftObservableSignaturePressureTest
    shiftNextPoint
shiftNextPromotionReadyPoint =
  OSPT.promotionReadyPressurePoint
    shiftObservableSignaturePressureTest
    shiftNextPoint
    shiftNextObservableForced
    shiftNextSignatureForced

shiftHeldExitObservableHeld :
  OTGE.status shiftObservableGate shiftHeldExitPoint ≡ OTGE.held
shiftHeldExitObservableHeld = refl

shiftHeldExitSignatureHeld :
  ACSS.status shiftSignatureStress shiftHeldExitPoint ≡ ACSS.held
shiftHeldExitSignatureHeld = refl

shiftHeldExitPressureHeld :
  OSPT.pressureStatus
    shiftObservableSignaturePressureTest
    shiftHeldExitPoint
  ≡
  OSPT.held
shiftHeldExitPressureHeld = refl

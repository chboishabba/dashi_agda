module DASHI.Physics.Closure.KnownLimitsInterpretableObservableConsumer where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAGMI
open import DASHI.Physics.Closure.CanonicalGaugeMatterInterpretableObservableTheorem as CGMIOT
open import DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem as KLBGT
open import DASHI.Physics.Closure.KnownLimitsQFTBridgeTheorem as KLBQFT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI

record KnownLimitsInterpretableObservableConsumer : Setω where
  field
    grBridge : KLBGT.KnownLimitsGRBridgeTheorem
    qftBridge : KLBQFT.KnownLimitsQFTBridgeTheorem
    grInterpretableObservable :
      CGMIOT.CanonicalGaugeMatterInterpretableObservableTheorem
    qftInterpretableObservable :
      CGMIOT.CanonicalGaugeMatterInterpretableObservableTheorem

    canonicalChargeStable :
      ∀ x →
      CAGMI.canonicalConservedChargeOf x
        ≡
      CAGMI.canonicalConservedChargeOf (CAGMI.canonicalClosureDynamics x)

    coarseChargeTracksTransportedSchedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAGMI.canonicalTransportState x) →
      CAGMI.canonicalCoarseConservedChargeOf x
        ≡
      CAGMI.projectTransportedShiftCoarseCharge
        (SRGOI.shiftCoarseAlt (CAGMI.canonicalTransportState x))

canonicalKnownLimitsInterpretableObservableConsumer :
  KnownLimitsInterpretableObservableConsumer
canonicalKnownLimitsInterpretableObservableConsumer =
  record
    { grBridge = KLBGT.canonicalKnownLimitsGRBridgeTheorem
    ; qftBridge = KLBQFT.canonicalKnownLimitsQFTBridgeTheorem
    ; grInterpretableObservable =
        KLBGT.KnownLimitsGRBridgeTheorem.interpretableObservableRecovery
          KLBGT.canonicalKnownLimitsGRBridgeTheorem
    ; qftInterpretableObservable =
        KLBQFT.KnownLimitsQFTBridgeTheorem.interpretableObservableRecovery
          KLBQFT.canonicalKnownLimitsQFTBridgeTheorem
    ; canonicalChargeStable = CAGMI.canonicalConservedChargePreserved
    ; coarseChargeTracksTransportedSchedule =
        CAGMI.canonicalSourceCoarseCharge-to-schedule
    }

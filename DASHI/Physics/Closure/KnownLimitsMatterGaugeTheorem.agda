module DASHI.Physics.Closure.KnownLimitsMatterGaugeTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalGaugeConstraintBridgeTheorem as CGCBT
open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem as SLLB

record KnownLimitsMatterGaugeTheorem : Setω where
  field
    spinLocalLorentzBridge : SLLB.SpinLocalLorentzBridge
      MCCSI.minimumCredibleClosureShift
    gaugeConstraintBridge :
      CGCBT.CanonicalGaugeConstraintBridgeTheorem
    spinDiracConsumer :
      CSDC.SpinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    canonicalRecoveryWitness : KLRW.KnownLimitsRecoveryWitnessPlus

canonicalKnownLimitsMatterGaugeTheorem :
  KnownLimitsMatterGaugeTheorem
canonicalKnownLimitsMatterGaugeTheorem =
  record
    { spinLocalLorentzBridge = SLLB.canonicalSpinLocalLorentzBridge
    ; gaugeConstraintBridge = CGCBT.canonicalGaugeConstraintBridgeTheorem
    ; spinDiracConsumer =
        CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    ; canonicalRecoveryWitness = KLRW.canonicalKnownLimitsRecoveryWitness
    }

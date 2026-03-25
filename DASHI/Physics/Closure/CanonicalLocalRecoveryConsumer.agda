module DASHI.Physics.Closure.CanonicalLocalRecoveryConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem as KLET
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

localRecoveryFromWitness :
  KLRW.KnownLimitsRecoveryWitnessPlus →
  KLRT.KnownLimitsLocalRecoveryTheorem
localRecoveryFromWitness witness =
  record
    { localLorentzRecovered =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzRecovered witness
    ; propagationLimitRecovered =
        KLRW.KnownLimitsRecoveryWitnessPlus.propagationLimitRecovered witness
    ; propagationWitness =
        KLRW.KnownLimitsRecoveryWitnessPlus.propagationWitness witness
    ; localLorentzOrthogonality =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzOrthogonality witness
    ; localLorentzPolarization =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzPolarization witness
    }

effectiveGeometryFromWitness :
  KLRW.KnownLimitsRecoveryWitnessPlus → KLET.KnownLimitsEffectiveGeometryTheorem
effectiveGeometryFromWitness witness =
  record
    { localLorentzRecovered =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzRecovered witness
    ; propagationLimitRecovered =
        KLRW.KnownLimitsRecoveryWitnessPlus.propagationLimitRecovered witness
    ; propagationSeams =
        KLRW.KnownLimitsRecoveryWitnessPlus.propagationWitness witness
    ; effectiveOrthogonality =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzOrthogonality witness
    ; effectivePolarization =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzPolarization witness
    }

localRecoveryFromConsumer :
  (C : MCPC.MinimalCrediblePhysicsClosure) →
  CSDC.SpinDiracConsumerFromMinimal C →
  KLRT.KnownLimitsLocalRecoveryTheorem
localRecoveryFromConsumer _ consumer =
  localRecoveryFromWitness
    (CSDC.SpinDiracConsumerFromMinimal.knownLimitsRecoveryWitnessPlus consumer)

effectiveGeometryFromConsumer :
  (C : MCPC.MinimalCrediblePhysicsClosure) →
  CSDC.SpinDiracConsumerFromMinimal C →
  KLET.KnownLimitsEffectiveGeometryTheorem
effectiveGeometryFromConsumer _ consumer =
  effectiveGeometryFromWitness
    (CSDC.SpinDiracConsumerFromMinimal.knownLimitsRecoveryWitnessPlus consumer)

record LocalRecoveryConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    spinDiracConsumer : CSDC.SpinDiracConsumerFromMinimal C
    knownLimitsLocalRecovery : KLRT.KnownLimitsLocalRecoveryTheorem
    knownLimitsEffectiveGeometry : KLET.KnownLimitsEffectiveGeometryTheorem

canonicalLocalRecoveryConsumer :
  LocalRecoveryConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalLocalRecoveryConsumer =
  let consumer =
        CSDC.spinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
  in
    record
      { spinDiracConsumer = consumer
      ; knownLimitsLocalRecovery =
          localRecoveryFromConsumer
            MCCSI.minimumCredibleClosureShift
            consumer
      ; knownLimitsEffectiveGeometry =
          effectiveGeometryFromConsumer
            MCCSI.minimumCredibleClosureShift
            consumer
      }

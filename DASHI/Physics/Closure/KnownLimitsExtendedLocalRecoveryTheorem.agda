module DASHI.Physics.Closure.KnownLimitsExtendedLocalRecoveryTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC
open import DASHI.Physics.Closure.KnownLimitsGeometryTransportTheorem as KLGT
open import DASHI.Physics.Closure.KnownLimitsLocalCoherenceTheorem as KLLCT
open import DASHI.Physics.Closure.KnownLimitsPropagationSpinTheorem as KLPST
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsExtendedLocalRecoveryTheorem : Setω where
  field
    localCoherence : KLLCT.KnownLimitsLocalCoherenceTheorem
    geometryTransport : KLGT.KnownLimitsGeometryTransportTheorem
    propagationSpin : KLPST.KnownLimitsPropagationSpinTheorem
    canonicalConsumer :
      CSDC.SpinDiracConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    recoveredPropagation : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    recoveredOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    recoveredPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsExtendedLocalRecoveryTheorem :
  KnownLimitsExtendedLocalRecoveryTheorem
canonicalKnownLimitsExtendedLocalRecoveryTheorem =
  record
    { localCoherence = KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; geometryTransport = KLGT.canonicalKnownLimitsGeometryTransportTheorem
    ; propagationSpin = KLPST.canonicalKnownLimitsPropagationSpinTheorem
    ; canonicalConsumer =
        KLPST.KnownLimitsPropagationSpinTheorem.canonicalConsumer
          KLPST.canonicalKnownLimitsPropagationSpinTheorem
    ; recoveredPropagation =
        KLLCT.KnownLimitsLocalCoherenceTheorem.coherentPropagation
          KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; recoveredOrthogonality =
        KLLCT.KnownLimitsLocalCoherenceTheorem.coherentOrthogonality
          KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; recoveredPolarization =
        KLLCT.KnownLimitsLocalCoherenceTheorem.coherentPolarization
          KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    }

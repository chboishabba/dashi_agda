module DASHI.Physics.Closure.KnownLimitsLocalPhysicsCoherenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.CanonicalPropagationConsumer as CPC
open import DASHI.Physics.Closure.KnownLimitsExtendedLocalRecoveryTheorem as KLER
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsLocalPhysicsCoherenceTheorem : Setω where
  field
    extendedRecovery : KLER.KnownLimitsExtendedLocalRecoveryTheorem
    propagationConsumer :
      CPC.PropagationConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    recoveredPropagation : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    recoveredOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    recoveredPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsLocalPhysicsCoherenceTheorem :
  KnownLimitsLocalPhysicsCoherenceTheorem
canonicalKnownLimitsLocalPhysicsCoherenceTheorem =
  record
    { extendedRecovery = KLER.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    ; propagationConsumer = CPC.canonicalPropagationConsumer
    ; recoveredPropagation =
        KLER.KnownLimitsExtendedLocalRecoveryTheorem.recoveredPropagation
          KLER.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    ; recoveredOrthogonality =
        KLER.KnownLimitsExtendedLocalRecoveryTheorem.recoveredOrthogonality
          KLER.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    ; recoveredPolarization =
        KLER.KnownLimitsExtendedLocalRecoveryTheorem.recoveredPolarization
          KLER.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    }

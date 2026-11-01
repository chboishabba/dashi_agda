module DASHI.Physics.Closure.KnownLimitsRecoveredLocalRegimeTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.CanonicalPropagationConsumer as CPC
open import DASHI.Physics.Closure.KnownLimitsLocalPhysicsCoherenceTheorem as KLLPC
open import DASHI.Physics.Closure.KnownLimitsExtendedLocalRecoveryTheorem as KLER
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsRecoveredLocalRegimeTheorem : Setω where
  field
    localPhysics : KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem
    extendedRecovery : KLER.KnownLimitsExtendedLocalRecoveryTheorem
    propagationConsumer :
      CPC.PropagationConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    recoveredPropagation : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    recoveredOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    recoveredPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsRecoveredLocalRegimeTheorem :
  KnownLimitsRecoveredLocalRegimeTheorem
canonicalKnownLimitsRecoveredLocalRegimeTheorem =
  record
    { localPhysics = KLLPC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem
    ; extendedRecovery = KLER.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    ; propagationConsumer = CPC.canonicalPropagationConsumer
    ; recoveredPropagation =
        KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem.recoveredPropagation
          KLLPC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem
    ; recoveredOrthogonality =
        KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem.recoveredOrthogonality
          KLLPC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem
    ; recoveredPolarization =
        KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem.recoveredPolarization
          KLLPC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem
    }

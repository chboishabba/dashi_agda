module DASHI.Physics.Closure.KnownLimitsRecoveredObservableGeometryTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.CanonicalGeometryConsumer as CGC
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservablesTheorem as KLROT
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsRecoveredObservableGeometryTheorem : Setω where
  field
    recoveredObservables : KLROT.KnownLimitsRecoveredObservablesTheorem
    geometryConsumer :
      CGC.GeometryConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    recoveredOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    recoveredPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsRecoveredObservableGeometryTheorem :
  KnownLimitsRecoveredObservableGeometryTheorem
canonicalKnownLimitsRecoveredObservableGeometryTheorem =
  record
    { recoveredObservables =
        KLROT.canonicalKnownLimitsRecoveredObservablesTheorem
    ; geometryConsumer = CGC.canonicalGeometryConsumer
    ; recoveredOrthogonality =
        DCW.DynamicalClosureWitness.effectiveGeometryOrthogonality
          (CGC.GeometryConsumerFromMinimal.dynamicsWitness
            CGC.canonicalGeometryConsumer)
    ; recoveredPolarization =
        DCW.DynamicalClosureWitness.effectiveGeometryPolarization
          (CGC.GeometryConsumerFromMinimal.dynamicsWitness
            CGC.canonicalGeometryConsumer)
    }

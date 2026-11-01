module DASHI.Physics.Closure.KnownLimitsGeometryTransportTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.KnownLimitsCausalPropagationTheorem as KLCPT
open import DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem as KLET
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsGeometryTransportTheorem : Setω where
  field
    localRecovery : KLRT.KnownLimitsLocalRecoveryTheorem
    effectiveGeometry : KLET.KnownLimitsEffectiveGeometryTheorem
    causalPropagation : KLCPT.KnownLimitsCausalPropagationTheorem
    geometryCompatiblePropagation : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    transportedOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    transportedPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsGeometryTransportTheorem :
  KnownLimitsGeometryTransportTheorem
canonicalKnownLimitsGeometryTransportTheorem =
  record
    { localRecovery = KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; effectiveGeometry = KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; causalPropagation = KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; geometryCompatiblePropagation =
        KLCPT.KnownLimitsCausalPropagationTheorem.propagationSeams
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; transportedOrthogonality =
        KLCPT.KnownLimitsCausalPropagationTheorem.effectiveOrthogonality
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; transportedPolarization =
        KLCPT.KnownLimitsCausalPropagationTheorem.effectivePolarization
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    }

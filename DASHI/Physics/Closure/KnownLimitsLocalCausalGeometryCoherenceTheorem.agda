module DASHI.Physics.Closure.KnownLimitsLocalCausalGeometryCoherenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.KnownLimitsCausalPropagationTheorem as KLCPT
open import DASHI.Physics.Closure.KnownLimitsGeometryTransportTheorem as KLGT
open import DASHI.Physics.Closure.KnownLimitsLocalCausalEffectivePropagationTheorem as KLCEPT
open import DASHI.Physics.Closure.KnownLimitsLocalCoherenceTheorem as KLLCT
open import DASHI.Physics.Closure.KnownLimitsRecoveryPackage as KLRP
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsLocalCausalGeometryCoherenceTheorem : Setω where
  field
    localCausalEffectivePropagation :
      KLCEPT.KnownLimitsLocalCausalEffectivePropagationTheorem
    geometryTransport : KLGT.KnownLimitsGeometryTransportTheorem
    localCoherence : KLLCT.KnownLimitsLocalCoherenceTheorem
    localCausalGeometryCoherent :
      KLRP.KnownLimitsRecoveryPackage.causalStatus
        (KLCPT.KnownLimitsCausalPropagationTheorem.recoveryPackage
           (KLLCT.KnownLimitsLocalCoherenceTheorem.causalPropagation
              localCoherence))
      ≡ DCS.seamBackedCausalAdmissibility
    coherentPropagation : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    coherentOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    coherentPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsLocalCausalGeometryCoherenceTheorem :
  KnownLimitsLocalCausalGeometryCoherenceTheorem
canonicalKnownLimitsLocalCausalGeometryCoherenceTheorem =
  record
    { localCausalEffectivePropagation =
        KLCEPT.canonicalKnownLimitsLocalCausalEffectivePropagationTheorem
    ; geometryTransport = KLGT.canonicalKnownLimitsGeometryTransportTheorem
    ; localCoherence = KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; localCausalGeometryCoherent =
        KLLCT.KnownLimitsLocalCoherenceTheorem.localCausalCoherent
          KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; coherentPropagation =
        KLLCT.KnownLimitsLocalCoherenceTheorem.coherentPropagation
          KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; coherentOrthogonality =
        KLLCT.KnownLimitsLocalCoherenceTheorem.coherentOrthogonality
          KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; coherentPolarization =
        KLLCT.KnownLimitsLocalCoherenceTheorem.coherentPolarization
          KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    }

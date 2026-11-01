module DASHI.Physics.Closure.KnownLimitsLocalCoherenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.KnownLimitsCausalPropagationTheorem as KLCPT
open import DASHI.Physics.Closure.KnownLimitsGeometryTransportTheorem as KLGT
open import DASHI.Physics.Closure.KnownLimitsRecoveryPackage as KLRP
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsLocalCoherenceTheorem : Setω where
  field
    causalPropagation : KLCPT.KnownLimitsCausalPropagationTheorem
    geometryTransport : KLGT.KnownLimitsGeometryTransportTheorem
    localCausalCoherent :
      KLRP.KnownLimitsRecoveryPackage.causalStatus
        (KLCPT.KnownLimitsCausalPropagationTheorem.recoveryPackage
           causalPropagation)
      ≡ DCS.seamBackedCausalAdmissibility
    coherentPropagation : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    coherentOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    coherentPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsLocalCoherenceTheorem :
  KnownLimitsLocalCoherenceTheorem
canonicalKnownLimitsLocalCoherenceTheorem =
  record
    { causalPropagation = KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; geometryTransport = KLGT.canonicalKnownLimitsGeometryTransportTheorem
    ; localCausalCoherent =
        KLCPT.KnownLimitsCausalPropagationTheorem.localCausalRecovered
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; coherentPropagation =
        KLGT.KnownLimitsGeometryTransportTheorem.geometryCompatiblePropagation
          KLGT.canonicalKnownLimitsGeometryTransportTheorem
    ; coherentOrthogonality =
        KLGT.KnownLimitsGeometryTransportTheorem.transportedOrthogonality
          KLGT.canonicalKnownLimitsGeometryTransportTheorem
    ; coherentPolarization =
        KLGT.KnownLimitsGeometryTransportTheorem.transportedPolarization
          KLGT.canonicalKnownLimitsGeometryTransportTheorem
    }

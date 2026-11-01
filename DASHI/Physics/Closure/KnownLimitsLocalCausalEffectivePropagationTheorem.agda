module DASHI.Physics.Closure.KnownLimitsLocalCausalEffectivePropagationTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.KnownLimitsCausalPropagationTheorem as KLCPT
open import DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem as KLET
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT
open import DASHI.Physics.Closure.KnownLimitsRecoveryPackage as KLRP
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsLocalCausalEffectivePropagationTheorem : Setω where
  field
    localRecovery : KLRT.KnownLimitsLocalRecoveryTheorem
    effectiveGeometry : KLET.KnownLimitsEffectiveGeometryTheorem
    causalPropagation : KLCPT.KnownLimitsCausalPropagationTheorem
    localCausalEffectiveRecovered :
      KLRP.KnownLimitsRecoveryPackage.causalStatus
        (KLCPT.KnownLimitsCausalPropagationTheorem.recoveryPackage
           causalPropagation)
      ≡ DCS.seamBackedCausalAdmissibility
    recoveredPropagation : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    recoveredCausalAdmissibility : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    recoveredOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    recoveredPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsLocalCausalEffectivePropagationTheorem :
  KnownLimitsLocalCausalEffectivePropagationTheorem
canonicalKnownLimitsLocalCausalEffectivePropagationTheorem =
  record
    { localRecovery = KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; effectiveGeometry = KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; causalPropagation = KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; localCausalEffectiveRecovered =
        KLCPT.KnownLimitsCausalPropagationTheorem.localCausalRecovered
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; recoveredPropagation =
        KLCPT.KnownLimitsCausalPropagationTheorem.propagationSeams
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; recoveredCausalAdmissibility =
        KLCPT.KnownLimitsCausalPropagationTheorem.causalAdmissibility
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; recoveredOrthogonality =
        KLCPT.KnownLimitsCausalPropagationTheorem.effectiveOrthogonality
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    ; recoveredPolarization =
        KLCPT.KnownLimitsCausalPropagationTheorem.effectivePolarization
          KLCPT.canonicalKnownLimitsCausalPropagationTheorem
    }

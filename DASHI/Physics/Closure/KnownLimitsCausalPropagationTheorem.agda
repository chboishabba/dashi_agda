module DASHI.Physics.Closure.KnownLimitsCausalPropagationTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureShiftWitnessInstance as DCWSI
open import DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem as KLET
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT
open import DASHI.Physics.Closure.KnownLimitsRecoveryPackage as KLRP
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsCausalPropagationTheorem : Setω where
  field
    recoveryPackage : KLRP.KnownLimitsRecoveryPackage
    localRecovery : KLRT.KnownLimitsLocalRecoveryTheorem
    effectiveGeometry : KLET.KnownLimitsEffectiveGeometryTheorem
    localCausalRecovered :
      KLRP.KnownLimitsRecoveryPackage.causalStatus recoveryPackage
      ≡ DCS.seamBackedCausalAdmissibility
    propagationSeams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    causalAdmissibility : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    effectiveOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    effectivePolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsRecoveryPackage : KLRP.KnownLimitsRecoveryPackage
canonicalKnownLimitsRecoveryPackage =
  record
    { localRecovery = KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; effectiveGeometry = KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; propagationSeams =
        KLET.KnownLimitsEffectiveGeometryTheorem.propagationSeams
          KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; causalAdmissibility =
        λ {m} {k} →
          DCW.DynamicalClosureWitness.causalAdmissibilitySeams
            DCWSI.shiftDynamicsWitness
    ; causalStatus = DCS.seamBackedCausalAdmissibility
    ; effectiveOrthogonality =
        KLET.KnownLimitsEffectiveGeometryTheorem.effectiveOrthogonality
          KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; effectivePolarization =
        KLET.KnownLimitsEffectiveGeometryTheorem.effectivePolarization
          KLET.canonicalKnownLimitsEffectiveGeometryTheorem
    ; causalStatusRecovered = refl
    }

canonicalKnownLimitsCausalPropagationTheorem :
  KnownLimitsCausalPropagationTheorem
canonicalKnownLimitsCausalPropagationTheorem =
  record
    { recoveryPackage = canonicalKnownLimitsRecoveryPackage
    ; localRecovery = KLRP.localRecovery canonicalKnownLimitsRecoveryPackage
    ; effectiveGeometry = KLRP.effectiveGeometry canonicalKnownLimitsRecoveryPackage
    ; localCausalRecovered =
        KLRP.causalStatusRecovered canonicalKnownLimitsRecoveryPackage
    ; propagationSeams = KLRP.propagationSeams canonicalKnownLimitsRecoveryPackage
    ; causalAdmissibility = KLRP.causalAdmissibility canonicalKnownLimitsRecoveryPackage
    ; effectiveOrthogonality =
        KLRP.effectiveOrthogonality canonicalKnownLimitsRecoveryPackage
    ; effectivePolarization =
        KLRP.effectivePolarization canonicalKnownLimitsRecoveryPackage
    }

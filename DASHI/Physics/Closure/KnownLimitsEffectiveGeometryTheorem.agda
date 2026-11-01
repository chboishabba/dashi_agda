module DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT
open import DASHI.Physics.Closure.KnownLimitsStatus as KLS
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsEffectiveGeometryTheorem : Setω where
  field
    localLorentzRecovered :
      KLS.KnownLimitsStatus.localLorentz KLS.canonicalKnownLimitsStatus
      ≡ KLS.localLorentzTheoremBacked
    propagationLimitRecovered :
      KLS.KnownLimitsStatus.propagationLimit KLS.canonicalKnownLimitsStatus
      ≡ KLS.propagationLimitSeamBacked
    propagationSeams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    effectiveOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    effectivePolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsEffectiveGeometryTheorem :
  KnownLimitsEffectiveGeometryTheorem
canonicalKnownLimitsEffectiveGeometryTheorem =
  record
    { localLorentzRecovered =
        KLRT.KnownLimitsLocalRecoveryTheorem.localLorentzRecovered
          KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; propagationLimitRecovered =
        KLRT.KnownLimitsLocalRecoveryTheorem.propagationLimitRecovered
          KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; propagationSeams =
        KLRT.KnownLimitsLocalRecoveryTheorem.propagationWitness
          KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; effectiveOrthogonality =
        KLRT.KnownLimitsLocalRecoveryTheorem.localLorentzOrthogonality
          KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    ; effectivePolarization =
        KLRT.KnownLimitsLocalRecoveryTheorem.localLorentzPolarization
          KLRT.canonicalKnownLimitsLocalRecoveryTheorem
    }

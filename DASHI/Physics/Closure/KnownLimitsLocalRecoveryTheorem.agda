module DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW
open import DASHI.Physics.Closure.KnownLimitsStatus as KLS
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsLocalRecoveryTheorem : Setω where
  field
    localLorentzRecovered :
      KLS.KnownLimitsStatus.localLorentz KLS.canonicalKnownLimitsStatus
      ≡ KLS.localLorentzTheoremBacked
    propagationLimitRecovered :
      KLS.KnownLimitsStatus.propagationLimit KLS.canonicalKnownLimitsStatus
      ≡ KLS.propagationLimitSeamBacked
    propagationWitness : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    localLorentzOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    localLorentzPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

canonicalKnownLimitsLocalRecoveryTheorem :
  KnownLimitsLocalRecoveryTheorem
canonicalKnownLimitsLocalRecoveryTheorem =
  record
    { localLorentzRecovered =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzRecovered
          KLRW.canonicalKnownLimitsRecoveryWitness
    ; propagationLimitRecovered =
        KLRW.KnownLimitsRecoveryWitnessPlus.propagationLimitRecovered
          KLRW.canonicalKnownLimitsRecoveryWitness
    ; propagationWitness =
        KLRW.KnownLimitsRecoveryWitnessPlus.propagationWitness
          KLRW.canonicalKnownLimitsRecoveryWitness
    ; localLorentzOrthogonality =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzOrthogonality
          KLRW.canonicalKnownLimitsRecoveryWitness
    ; localLorentzPolarization =
        KLRW.KnownLimitsRecoveryWitnessPlus.localLorentzPolarization
          KLRW.canonicalKnownLimitsRecoveryWitness
    }

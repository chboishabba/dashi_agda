module DASHI.Physics.Closure.KnownLimitsRecoveryWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.DynamicalClosureShiftWitnessInstance as DCWI
open import DASHI.Physics.Closure.KnownLimitsRecovery as KLR
open import DASHI.Physics.Closure.KnownLimitsStatus as KLS
open import DASHI.Physics.Closure.OrthogonalityZLift as OZ
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

record KnownLimitsRecoveryWitnessPlus : Setω where
  field
    statusRecovery : KLR.KnownLimitsRecoveryWitness
    propagationWitness : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    localLorentzOrthogonality : ∀ {m : Nat} → OZ.OrthogonalityZLift {m}
    localLorentzPolarization :
      ∀ {m : Nat} →
      OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
    localLorentzRecovered :
      KLS.KnownLimitsStatus.localLorentz KLS.canonicalKnownLimitsStatus
      ≡ KLS.localLorentzTheoremBacked
    grLikeRecovered :
      KLS.KnownLimitsStatus.grLike KLS.canonicalKnownLimitsStatus
      ≡ KLS.grLikeTheoremBacked
    qftLikeRecovered :
      KLS.KnownLimitsStatus.qftLike KLS.canonicalKnownLimitsStatus
      ≡ KLS.qftLikeTheoremBacked
    propagationLimitRecovered :
      KLS.KnownLimitsStatus.propagationLimit KLS.canonicalKnownLimitsStatus
      ≡ KLS.propagationLimitSeamBacked

canonicalKnownLimitsRecoveryWitness : KnownLimitsRecoveryWitnessPlus
canonicalKnownLimitsRecoveryWitness =
  record
    { statusRecovery = KLR.canonicalKnownLimitsRecovery
    ; propagationWitness =
        DCW.DynamicalClosureWitness.propagationSeams DCWI.shiftDynamicsWitness
    ; localLorentzOrthogonality =
        DCW.DynamicalClosureWitness.effectiveGeometryOrthogonality
          DCWI.shiftDynamicsWitness
    ; localLorentzPolarization =
        DCW.DynamicalClosureWitness.effectiveGeometryPolarization
          DCWI.shiftDynamicsWitness
    ; localLorentzRecovered = refl
    ; grLikeRecovered = refl
    ; qftLikeRecovered = refl
    ; propagationLimitRecovered = refl
    }

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanEquation119DerivativeDoesNotDetermineAverageRound204Exact where

------------------------------------------------------------------------
-- ROUND204 BIDI / NON-FACTORABILITY: AN INDEPENDENT PRIMED OBSERVATION DOES
-- NOT DETERMINE THE ONE-STEP Q SOURCE.
--
-- Historical note. Earlier owners interpreted the printed CMP98 Q'(V0) from
-- Eq. (119) as a background derivative of Q(V0). The source audit does not
-- license that interpretation merely from the prime notation: Eq. (119) occurs
-- in the intermediate V1 expansion, whereas nonlinear Q(V0,A,c) and its final
-- linear form Q(V0)A are introduced later in (121)--(124).
--
-- The theorem below is purely structural and remains valid: if two systems have
-- the same auxiliary primed observation and different q values, no recovery
-- function depending only on that observation can reconstruct q. R211 recovers
-- qSource from the actual Eq. (124) linear-form owner instead.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126

boolAdditiveCarrier : R126.AdditiveOperatorCarrier
boolAdditiveCarrier = record
  { R126.AdditiveOperatorCarrier.Vector = Bool
  ; R126.AdditiveOperatorCarrier.zeroV = false
  ; R126.AdditiveOperatorCarrier.addV = λ left right → left
  }

qLeft : Nat → R126.Operator boolAdditiveCarrier
qLeft _ _ = false

qRight : Nat → R126.Operator boolAdditiveCarrier
qRight _ _ = true

sharedQPrime : Nat → R126.Operator boolAdditiveCarrier
sharedQPrime _ _ = false

leftOneStepSystem : R126.OneStepAveragingDerivative boolAdditiveCarrier
leftOneStepSystem = record
  { R126.OneStepAveragingDerivative.q = qLeft
  ; R126.OneStepAveragingDerivative.qPrime = sharedQPrime
  }

rightOneStepSystem : R126.OneStepAveragingDerivative boolAdditiveCarrier
rightOneStepSystem = record
  { R126.OneStepAveragingDerivative.q = qRight
  ; R126.OneStepAveragingDerivative.qPrime = sharedQPrime
  }

samePrimeObservation :
  ∀ step input →
  R126.qPrime leftOneStepSystem step input
  ≡ R126.qPrime rightOneStepSystem step input
samePrimeObservation step input = refl

-- Historical exported name retained for downstream compatibility only.
sameDerivativeObservation :
  ∀ step input →
  R126.qPrime leftOneStepSystem step input
  ≡ R126.qPrime rightOneStepSystem step input
sameDerivativeObservation = samePrimeObservation

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

differentQObservation :
  ∀ step input →
  R126.q leftOneStepSystem step input
  ≡ R126.q rightOneStepSystem step input → ⊥
differentQObservation step input equality = falseNotTrue equality

-- Historical exported name retained for downstream compatibility only.
differentAverageObservation :
  ∀ step input →
  R126.q leftOneStepSystem step input
  ≡ R126.q rightOneStepSystem step input → ⊥
differentAverageObservation = differentQObservation

record QPrimeFactorization
    (observePrime :
      R126.OneStepAveragingDerivative boolAdditiveCarrier → Bool)
    (recoverQ : Bool → Bool) : Set where
  field
    factors : ∀ system →
      recoverQ (observePrime system)
      ≡ R126.q system 0 false

open QPrimeFactorization public

primeCollisionBlocksQRecovery :
  ∀ (observePrime :
      R126.OneStepAveragingDerivative boolAdditiveCarrier → Bool)
    (recoverQ : Bool → Bool) →
  observePrime leftOneStepSystem ≡ observePrime rightOneStepSystem →
  QPrimeFactorization observePrime recoverQ →
  ⊥
primeCollisionBlocksQRecovery observePrime recoverQ collision factorization =
  falseNotTrue
    (let
      leftFactor = factors factorization leftOneStepSystem
      rightFactor = factors factorization rightOneStepSystem
    in
    trans
      (sym leftFactor)
      (trans
        (cong recoverQ collision)
        rightFactor))

-- Historical exported theorem name retained for downstream compatibility only.
derivativeCollisionBlocksQRecovery :
  ∀ (observePrime :
      R126.OneStepAveragingDerivative boolAdditiveCarrier → Bool)
    (recoverQ : Bool → Bool) →
  observePrime leftOneStepSystem ≡ observePrime rightOneStepSystem →
  QPrimeFactorization observePrime recoverQ →
  ⊥
derivativeCollisionBlocksQRecovery = primeCollisionBlocksQRecovery

equation119DerivativeCollisionRound204Level : ProofLevel
equation119DerivativeCollisionRound204Level = machineChecked

qSourceDoesNotFollowFromQPrimeRound204Level : ProofLevel
qSourceDoesNotFollowFromQPrimeRound204Level = machineChecked

-- Superseded as the source target by R211. The actual qSource route is the
-- Eq. (122)--(124) linear form, not reconstruction from Eq. (119).
literalCMP98OneStepAverageQSourceSameObjectRound204Level : ProofLevel
literalCMP98OneStepAverageQSourceSameObjectRound204Level = conditional

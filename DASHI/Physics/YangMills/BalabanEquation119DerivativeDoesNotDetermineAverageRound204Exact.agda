{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanEquation119DerivativeDoesNotDetermineAverageRound204Exact where

------------------------------------------------------------------------
-- ROUND204 BIDI / NON-FACTORABILITY: Q'(V0) DOES NOT DETERMINE Q(V0).
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

sameDerivativeObservation :
  ∀ step input →
  R126.qPrime leftOneStepSystem step input
  ≡ R126.qPrime rightOneStepSystem step input
sameDerivativeObservation step input = refl

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

differentAverageObservation :
  ∀ step input →
  R126.q leftOneStepSystem step input
  ≡ R126.q rightOneStepSystem step input → ⊥
differentAverageObservation step input equality = falseNotTrue equality

record QPrimeFactorization
    (observePrime :
      R126.OneStepAveragingDerivative boolAdditiveCarrier → Bool)
    (recoverQ : Bool → Bool) : Set where
  field
    factors : ∀ system →
      recoverQ (observePrime system)
      ≡ R126.q system 0 false

open QPrimeFactorization public

derivativeCollisionBlocksQRecovery :
  ∀ (observePrime :
      R126.OneStepAveragingDerivative boolAdditiveCarrier → Bool)
    (recoverQ : Bool → Bool) →
  observePrime leftOneStepSystem ≡ observePrime rightOneStepSystem →
  QPrimeFactorization observePrime recoverQ →
  ⊥
derivativeCollisionBlocksQRecovery observePrime recoverQ collision factorization =
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

equation119DerivativeCollisionRound204Level : ProofLevel
equation119DerivativeCollisionRound204Level = machineChecked

qSourceDoesNotFollowFromQPrimeRound204Level : ProofLevel
qSourceDoesNotFollowFromQPrimeRound204Level = machineChecked

literalCMP98OneStepAverageQSourceSameObjectRound204Level : ProofLevel
literalCMP98OneStepAverageQSourceSameObjectRound204Level = conditional

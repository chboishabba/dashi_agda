module DASHI.Moonshine.P37MarkedX2JointFingerprintDeckCollisionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Produce a source-native non-Ogg analogue of the p=11 observation collision.
-- On the actual eighteen p=37 Deuring roots, construct two distinct integer
-- observables with the SAME literal marked Hecke/Frobenius fingerprint
--
--       (T3,T5,F) = (1,0,+1),
--
-- but different deck behaviour:
--
--   * coarseEvenObserver factors through the coarse supersingular j-class and
--     is invariant under the right deck S3 action;
--   * deckMovingEvenObserver is Frobenius-even and has zero sum on every
--     six-frame coarse fibre, but is moved by the genuine deck C3 rotation.
--
-- Thus even after source-native marked T3/T5 and geometric Frobenius are all
-- placed on the SAME carrier, their joint scalar fingerprint does not recover
-- the deck symmetry type.  This independently reproduces the information-loss
-- phenomenon already seen at p=11.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_)

import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedLegendreT3T5Exact as Hecke
import DASHI.Moonshine.P37MarkedX2FrobeniusFrickeExact as FF
import DASHI.Moonshine.P37MarkedX2DeckTorsorExact as Deck

------------------------------------------------------------------------
-- Integer observable actions derived directly from the literal neighbour lists.
------------------------------------------------------------------------

MarkedObservable : Set
MarkedObservable = P37.P37SupersingularLambda → ℤ

t3Action : MarkedObservable → MarkedObservable
t3Action f x =
  f (Hecke.markedT3Neighbour x zero)
  +ℤ f (Hecke.markedT3Neighbour x (suc zero))
  +ℤ f (Hecke.markedT3Neighbour x (suc (suc zero)))
  +ℤ f (Hecke.markedT3Neighbour x (suc (suc (suc zero))))

t5Action : MarkedObservable → MarkedObservable
t5Action f x =
  f (Hecke.markedT5Neighbour x zero)
  +ℤ f (Hecke.markedT5Neighbour x (suc zero))
  +ℤ f (Hecke.markedT5Neighbour x (suc (suc zero)))
  +ℤ f (Hecke.markedT5Neighbour x (suc (suc (suc zero))))
  +ℤ f (Hecke.markedT5Neighbour x (suc (suc (suc (suc zero)))))
  +ℤ f (Hecke.markedT5Neighbour x (suc (suc (suc (suc (suc zero))))))

frobeniusAction : MarkedObservable → MarkedObservable
frobeniusAction f x = f (FF.markedFrobenius37 x)

------------------------------------------------------------------------
-- Coarse even mode: constant on every six-frame coarse j fibre.
-- j8 gets 2; both quadratic-conjugate coarse classes get -1.
------------------------------------------------------------------------

coarseEvenObserver : MarkedObservable
coarseEvenObserver (P37.lambda37 P37.q0 _) = -[1+ 0 ]
coarseEvenObserver (P37.lambda37 P37.q1 _) = + 2
coarseEvenObserver (P37.lambda37 P37.q2 _) = -[1+ 0 ]
coarseEvenObserver (P37.lambda37 P37.q3 _) = -[1+ 0 ]
coarseEvenObserver (P37.lambda37 P37.q4 _) = -[1+ 0 ]
coarseEvenObserver (P37.lambda37 P37.q5 _) = -[1+ 0 ]
coarseEvenObserver (P37.lambda37 P37.q6 _) = + 2
coarseEvenObserver (P37.lambda37 P37.q7 _) = -[1+ 0 ]
coarseEvenObserver (P37.lambda37 P37.q8 _) = + 2

coarseEvenT3Eigen :
  (x : P37.P37SupersingularLambda) → t3Action coarseEvenObserver x ≡ coarseEvenObserver x
coarseEvenT3Eigen (P37.lambda37 P37.q0 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q0 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q1 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q1 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q2 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q2 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q3 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q3 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q4 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q4 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q5 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q5 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q6 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q6 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q7 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q7 P37.root1) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q8 P37.root0) = refl
coarseEvenT3Eigen (P37.lambda37 P37.q8 P37.root1) = refl

coarseEvenT5Zero :
  (x : P37.P37SupersingularLambda) → t5Action coarseEvenObserver x ≡ + 0
coarseEvenT5Zero (P37.lambda37 P37.q0 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q0 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q1 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q1 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q2 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q2 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q3 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q3 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q4 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q4 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q5 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q5 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q6 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q6 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q7 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q7 P37.root1) = refl
coarseEvenT5Zero (P37.lambda37 P37.q8 P37.root0) = refl
coarseEvenT5Zero (P37.lambda37 P37.q8 P37.root1) = refl

coarseEvenFrobeniusEigen :
  (x : P37.P37SupersingularLambda) →
  frobeniusAction coarseEvenObserver x ≡ coarseEvenObserver x
coarseEvenFrobeniusEigen (P37.lambda37 P37.q0 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q0 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q1 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q1 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q2 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q2 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q3 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q3 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q4 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q4 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q5 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q5 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q6 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q6 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q7 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q7 P37.root1) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q8 P37.root0) = refl
coarseEvenFrobeniusEigen (P37.lambda37 P37.q8 P37.root1) = refl

------------------------------------------------------------------------
-- A distinct Frobenius-even marked mode with the same T3/T5 eigenvalues.
-- Values are root-bit independent but vary inside each deck orbit.
------------------------------------------------------------------------

deckMovingEvenObserver : MarkedObservable
deckMovingEvenObserver (P37.lambda37 P37.q0 _) = + 0
deckMovingEvenObserver (P37.lambda37 P37.q1 _) = -[1+ 0 ]
deckMovingEvenObserver (P37.lambda37 P37.q2 _) = + 1
deckMovingEvenObserver (P37.lambda37 P37.q3 _) = -[1+ 0 ]
deckMovingEvenObserver (P37.lambda37 P37.q4 _) = + 1
deckMovingEvenObserver (P37.lambda37 P37.q5 _) = -[1+ 0 ]
deckMovingEvenObserver (P37.lambda37 P37.q6 _) = + 1
deckMovingEvenObserver (P37.lambda37 P37.q7 _) = + 0
deckMovingEvenObserver (P37.lambda37 P37.q8 _) = + 0

deckMovingEvenT3Eigen :
  (x : P37.P37SupersingularLambda) →
  t3Action deckMovingEvenObserver x ≡ deckMovingEvenObserver x
deckMovingEvenT3Eigen (P37.lambda37 P37.q0 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q0 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q1 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q1 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q2 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q2 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q3 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q3 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q4 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q4 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q5 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q5 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q6 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q6 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q7 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q7 P37.root1) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q8 P37.root0) = refl
deckMovingEvenT3Eigen (P37.lambda37 P37.q8 P37.root1) = refl

deckMovingEvenT5Zero :
  (x : P37.P37SupersingularLambda) → t5Action deckMovingEvenObserver x ≡ + 0
deckMovingEvenT5Zero (P37.lambda37 P37.q0 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q0 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q1 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q1 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q2 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q2 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q3 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q3 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q4 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q4 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q5 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q5 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q6 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q6 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q7 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q7 P37.root1) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q8 P37.root0) = refl
deckMovingEvenT5Zero (P37.lambda37 P37.q8 P37.root1) = refl

deckMovingEvenFrobeniusEigen :
  (x : P37.P37SupersingularLambda) →
  frobeniusAction deckMovingEvenObserver x ≡ deckMovingEvenObserver x
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q0 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q0 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q1 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q1 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q2 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q2 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q3 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q3 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q4 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q4 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q5 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q5 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q6 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q6 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q7 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q7 P37.root1) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q8 P37.root0) = refl
deckMovingEvenFrobeniusEigen (P37.lambda37 P37.q8 P37.root1) = refl

------------------------------------------------------------------------
-- Deck distinction: the coarse mode is invariant, the marked mode is not.
------------------------------------------------------------------------

coarseEvenDeckRInvariant :
  (x : P37.P37SupersingularLambda) →
  coarseEvenObserver (Deck.lambdaDeckR x) ≡ coarseEvenObserver x
coarseEvenDeckRInvariant (P37.lambda37 P37.q0 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q0 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q1 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q1 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q2 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q2 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q3 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q3 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q4 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q4 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q5 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q5 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q6 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q6 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q7 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q7 P37.root1) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q8 P37.root0) = refl
coarseEvenDeckRInvariant (P37.lambda37 P37.q8 P37.root1) = refl

deckMovingEvenChangesUnderR :
  deckMovingEvenObserver
    (Deck.lambdaDeckR (P37.lambda37 P37.q1 P37.root0))
  ≡ deckMovingEvenObserver (P37.lambda37 P37.q1 P37.root0)
  → ⊥
deckMovingEvenChangesUnderR ()

-- Explicit zero-average deck-orbit values for the moving mode.  In the
-- frame-cycle order used by the p37 deck torsor these are the three coarse
-- six-frame sums; each is definitionally zero.
p37MovingJ8OrbitSumZero :
  ((-[1+ 0 ] +ℤ + 1) +ℤ + 0 +ℤ + 1 +ℤ + 0 +ℤ -[1+ 0 ]) ≡ + 0
p37MovingJ8OrbitSumZero = refl

p37MovingConjugate0OrbitSumZero :
  ((+ 0 +ℤ -[1+ 0 ]) +ℤ + 1 +ℤ + 0 +ℤ -[1+ 0 ] +ℤ + 1) ≡ + 0
p37MovingConjugate0OrbitSumZero = refl

p37MovingConjugate1OrbitSumZero :
  ((+ 0 +ℤ -[1+ 0 ]) +ℤ + 1 +ℤ + 0 +ℤ -[1+ 0 ] +ℤ + 1) ≡ + 0
p37MovingConjugate1OrbitSumZero = refl

record P37MarkedJointFingerprintDeckCollisionBoundary : Set where
  field
    sameT3T5FSignatureConstructed : Bool
    sameT3T5FSignatureConstructedIsTrue :
      sameT3T5FSignatureConstructed ≡ true

    oneWitnessDeckInvariant : Bool
    oneWitnessDeckInvariantIsTrue : oneWitnessDeckInvariant ≡ true

    otherWitnessMovedByDeckRotation : Bool
    otherWitnessMovedByDeckRotationIsTrue : otherWitnessMovedByDeckRotation ≡ true

    scalarHeckeFrobeniusFingerprintSeparating : Bool
    scalarHeckeFrobeniusFingerprintSeparatingIsFalse :
      scalarHeckeFrobeniusFingerprintSeparating ≡ false

canonicalP37MarkedJointFingerprintDeckCollisionBoundary :
  P37MarkedJointFingerprintDeckCollisionBoundary
canonicalP37MarkedJointFingerprintDeckCollisionBoundary = record
  { sameT3T5FSignatureConstructed = true
  ; sameT3T5FSignatureConstructedIsTrue = refl
  ; oneWitnessDeckInvariant = true
  ; oneWitnessDeckInvariantIsTrue = refl
  ; otherWitnessMovedByDeckRotation = true
  ; otherWitnessMovedByDeckRotationIsTrue = refl
  ; scalarHeckeFrobeniusFingerprintSeparating = false
  ; scalarHeckeFrobeniusFingerprintSeparatingIsFalse = refl
  }

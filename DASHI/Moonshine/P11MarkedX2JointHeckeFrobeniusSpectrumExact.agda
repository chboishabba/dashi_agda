module DASHI.Moonshine.P11MarkedX2JointHeckeFrobeniusSpectrumExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight, "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Nicholas Katz and Barry Mazur, "Arithmetic Moduli of Elliptic Curves",
-- Annals of Mathematics Studies 108, Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
--
-- Toshitsune Miyake, "Modular Forms", Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Work on the SAME five-point marked X(2) supersingular carrier already
-- reconstructed from quaternion theta counts.  Linearise the literal positive
-- marked T3 and T5 neighbour systems over Q, add the geometric Frobenius /
-- marked Fricke involution, and compute the complete simultaneous invariant
-- decomposition.
--
-- Joint signatures:
--
--   constant/Perron line:       (T3,T5,F) = ( 4, 6,+1)
--   Frobenius-odd A-line:       (T3,T5,F) = ( 1,-3,-1)
--   remaining 3-dimensional:    (T3,T5,F) = (-1, 1,+1)
--
-- The last sector has multiplicity three, so the joint (T3,T5,F=Fricke)
-- spectrum does NOT yet isolate a one-dimensional Ogg fingerprint.  This is
-- an exact p=11 result on the source-native marked carrier, not a hand lift.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact as Marked
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact as Frob

Observable5 : Set
Observable5 = Fine.P11Fine5 → ℚ

markedT3 : Observable5 → Observable5
markedT3 observable state =
  Classical.foldFin _+_ 0ℚ
    (λ edge → observable (Marked.markedT3Neighbour state edge))

markedT5 : Observable5 → Observable5
markedT5 observable state =
  Classical.foldFin _+_ 0ℚ
    (λ edge → observable (Marked.markedT5Neighbour state edge))

frobeniusPullback : Observable5 → Observable5
frobeniusPullback observable state = observable (Frob.markedFrobenius state)

frickePullback : Observable5 → Observable5
frickePullback = frobeniusPullback

scale : ℚ → Observable5 → Observable5
scale coefficient observable state = coefficient * observable state

add : Observable5 → Observable5 → Observable5
add left right state = left state + right state

constantMode : Observable5
constantMode state = 1ℚ

aAntiMode : Observable5
aAntiMode Fine.a0 = 1ℚ
aAntiMode Fine.a1 = - 1ℚ
aAntiMode Fine.b0 = 0ℚ
aAntiMode Fine.b1 = 0ℚ
aAntiMode Fine.b2 = 0ℚ

mixedEvenMode : Observable5
mixedEvenMode Fine.a0 = - (+ 3 / 1)
mixedEvenMode Fine.a1 = - (+ 3 / 1)
mixedEvenMode Fine.b0 = + 2 / 1
mixedEvenMode Fine.b1 = + 2 / 1
mixedEvenMode Fine.b2 = + 2 / 1

bDiff01Mode : Observable5
bDiff01Mode Fine.a0 = 0ℚ
bDiff01Mode Fine.a1 = 0ℚ
bDiff01Mode Fine.b0 = 1ℚ
bDiff01Mode Fine.b1 = - 1ℚ
bDiff01Mode Fine.b2 = 0ℚ

bDiff02Mode : Observable5
bDiff02Mode Fine.a0 = 0ℚ
bDiff02Mode Fine.a1 = 0ℚ
bDiff02Mode Fine.b0 = 1ℚ
bDiff02Mode Fine.b1 = 0ℚ
bDiff02Mode Fine.b2 = - 1ℚ

constantT3Eigen : (state : Fine.P11Fine5) →
  markedT3 constantMode state ≡ (+ 4 / 1) * constantMode state
constantT3Eigen Fine.a0 = refl
constantT3Eigen Fine.a1 = refl
constantT3Eigen Fine.b0 = refl
constantT3Eigen Fine.b1 = refl
constantT3Eigen Fine.b2 = refl

constantT5Eigen : (state : Fine.P11Fine5) →
  markedT5 constantMode state ≡ (+ 6 / 1) * constantMode state
constantT5Eigen Fine.a0 = refl
constantT5Eigen Fine.a1 = refl
constantT5Eigen Fine.b0 = refl
constantT5Eigen Fine.b1 = refl
constantT5Eigen Fine.b2 = refl

constantFrobeniusEven : (state : Fine.P11Fine5) →
  frobeniusPullback constantMode state ≡ constantMode state
constantFrobeniusEven Fine.a0 = refl
constantFrobeniusEven Fine.a1 = refl
constantFrobeniusEven Fine.b0 = refl
constantFrobeniusEven Fine.b1 = refl
constantFrobeniusEven Fine.b2 = refl

aAntiT3Eigen : (state : Fine.P11Fine5) → markedT3 aAntiMode state ≡ aAntiMode state
aAntiT3Eigen Fine.a0 = refl
aAntiT3Eigen Fine.a1 = refl
aAntiT3Eigen Fine.b0 = refl
aAntiT3Eigen Fine.b1 = refl
aAntiT3Eigen Fine.b2 = refl

aAntiT5Eigen : (state : Fine.P11Fine5) →
  markedT5 aAntiMode state ≡ (- (+ 3 / 1)) * aAntiMode state
aAntiT5Eigen Fine.a0 = refl
aAntiT5Eigen Fine.a1 = refl
aAntiT5Eigen Fine.b0 = refl
aAntiT5Eigen Fine.b1 = refl
aAntiT5Eigen Fine.b2 = refl

aAntiFrobeniusOdd : (state : Fine.P11Fine5) →
  frobeniusPullback aAntiMode state ≡ - aAntiMode state
aAntiFrobeniusOdd Fine.a0 = refl
aAntiFrobeniusOdd Fine.a1 = refl
aAntiFrobeniusOdd Fine.b0 = refl
aAntiFrobeniusOdd Fine.b1 = refl
aAntiFrobeniusOdd Fine.b2 = refl

mixedT3Eigen : (state : Fine.P11Fine5) → markedT3 mixedEvenMode state ≡ - mixedEvenMode state
mixedT3Eigen Fine.a0 = refl
mixedT3Eigen Fine.a1 = refl
mixedT3Eigen Fine.b0 = refl
mixedT3Eigen Fine.b1 = refl
mixedT3Eigen Fine.b2 = refl

mixedT5Eigen : (state : Fine.P11Fine5) → markedT5 mixedEvenMode state ≡ mixedEvenMode state
mixedT5Eigen Fine.a0 = refl
mixedT5Eigen Fine.a1 = refl
mixedT5Eigen Fine.b0 = refl
mixedT5Eigen Fine.b1 = refl
mixedT5Eigen Fine.b2 = refl

mixedFrobeniusEven : (state : Fine.P11Fine5) → frobeniusPullback mixedEvenMode state ≡ mixedEvenMode state
mixedFrobeniusEven Fine.a0 = refl
mixedFrobeniusEven Fine.a1 = refl
mixedFrobeniusEven Fine.b0 = refl
mixedFrobeniusEven Fine.b1 = refl
mixedFrobeniusEven Fine.b2 = refl

bDiff01T3Eigen : (state : Fine.P11Fine5) → markedT3 bDiff01Mode state ≡ - bDiff01Mode state
bDiff01T3Eigen Fine.a0 = refl
bDiff01T3Eigen Fine.a1 = refl
bDiff01T3Eigen Fine.b0 = refl
bDiff01T3Eigen Fine.b1 = refl
bDiff01T3Eigen Fine.b2 = refl

bDiff01T5Eigen : (state : Fine.P11Fine5) → markedT5 bDiff01Mode state ≡ bDiff01Mode state
bDiff01T5Eigen Fine.a0 = refl
bDiff01T5Eigen Fine.a1 = refl
bDiff01T5Eigen Fine.b0 = refl
bDiff01T5Eigen Fine.b1 = refl
bDiff01T5Eigen Fine.b2 = refl

bDiff01FrobeniusEven : (state : Fine.P11Fine5) → frobeniusPullback bDiff01Mode state ≡ bDiff01Mode state
bDiff01FrobeniusEven Fine.a0 = refl
bDiff01FrobeniusEven Fine.a1 = refl
bDiff01FrobeniusEven Fine.b0 = refl
bDiff01FrobeniusEven Fine.b1 = refl
bDiff01FrobeniusEven Fine.b2 = refl

bDiff02T3Eigen : (state : Fine.P11Fine5) → markedT3 bDiff02Mode state ≡ - bDiff02Mode state
bDiff02T3Eigen Fine.a0 = refl
bDiff02T3Eigen Fine.a1 = refl
bDiff02T3Eigen Fine.b0 = refl
bDiff02T3Eigen Fine.b1 = refl
bDiff02T3Eigen Fine.b2 = refl

bDiff02T5Eigen : (state : Fine.P11Fine5) → markedT5 bDiff02Mode state ≡ bDiff02Mode state
bDiff02T5Eigen Fine.a0 = refl
bDiff02T5Eigen Fine.a1 = refl
bDiff02T5Eigen Fine.b0 = refl
bDiff02T5Eigen Fine.b1 = refl
bDiff02T5Eigen Fine.b2 = refl

bDiff02FrobeniusEven : (state : Fine.P11Fine5) → frobeniusPullback bDiff02Mode state ≡ bDiff02Mode state
bDiff02FrobeniusEven Fine.a0 = refl
bDiff02FrobeniusEven Fine.a1 = refl
bDiff02FrobeniusEven Fine.b0 = refl
bDiff02FrobeniusEven Fine.b1 = refl
bDiff02FrobeniusEven Fine.b2 = refl

markedT3T5Commute :
  (observable : Observable5) → (state : Fine.P11Fine5) →
  markedT3 (markedT5 observable) state ≡ markedT5 (markedT3 observable) state
markedT3T5Commute observable Fine.a0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3T5Commute observable Fine.a1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3T5Commute observable Fine.b0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3T5Commute observable Fine.b1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3T5Commute observable Fine.b2 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)

markedT3FrobeniusCommute :
  (observable : Observable5) → (state : Fine.P11Fine5) →
  markedT3 (frobeniusPullback observable) state ≡ frobeniusPullback (markedT3 observable) state
markedT3FrobeniusCommute observable Fine.a0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3FrobeniusCommute observable Fine.a1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3FrobeniusCommute observable Fine.b0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3FrobeniusCommute observable Fine.b1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT3FrobeniusCommute observable Fine.b2 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)

markedT5FrobeniusCommute :
  (observable : Observable5) → (state : Fine.P11Fine5) →
  markedT5 (frobeniusPullback observable) state ≡ frobeniusPullback (markedT5 observable) state
markedT5FrobeniusCommute observable Fine.a0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT5FrobeniusCommute observable Fine.a1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT5FrobeniusCommute observable Fine.b0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT5FrobeniusCommute observable Fine.b1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
markedT5FrobeniusCommute observable Fine.b2 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)

half third fifth : ℚ
half = + 1 / 2
third = + 1 / 3
fifth = + 1 / 5

coordAnti : Observable5 → ℚ
coordAnti observable = half * (observable Fine.a0 - observable Fine.a1)

coordAMean : Observable5 → ℚ
coordAMean observable = half * (observable Fine.a0 + observable Fine.a1)

coordBMean : Observable5 → ℚ
coordBMean observable = third * (observable Fine.b0 + observable Fine.b1 + observable Fine.b2)

coordMixed : Observable5 → ℚ
coordMixed observable = fifth * (coordBMean observable - coordAMean observable)

coordConstant : Observable5 → ℚ
coordConstant observable = fifth * ((+ 2 / 1) * coordAMean observable + (+ 3 / 1) * coordBMean observable)

coordBDiff01 : Observable5 → ℚ
coordBDiff01 observable = coordBMean observable - observable Fine.b1

coordBDiff02 : Observable5 → ℚ
coordBDiff02 observable = coordBMean observable - observable Fine.b2

reconstruct : Observable5 → Observable5
reconstruct observable state =
  coordConstant observable * constantMode state
  + coordAnti observable * aAntiMode state
  + coordMixed observable * mixedEvenMode state
  + coordBDiff01 observable * bDiff01Mode state
  + coordBDiff02 observable * bDiff02Mode state

jointBasisSpans :
  (observable : Observable5) → (state : Fine.P11Fine5) →
  reconstruct observable state ≡ observable state
jointBasisSpans observable Fine.a0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
jointBasisSpans observable Fine.a1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
jointBasisSpans observable Fine.b0 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
jointBasisSpans observable Fine.b1 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)
jointBasisSpans observable Fine.b2 = ℚRing.solve-∀ (observable Fine.a0) (observable Fine.a1) (observable Fine.b0) (observable Fine.b1) (observable Fine.b2)

record JointSpectrumBoundary : Set where
  constructor jointSpectrumBoundary
  field
    sourceNativeMarkedCarrierUsed : Bool
    t3T5FrobeniusCommute : Bool
    completeFiveModeDecomposition : Bool
    numberOfDistinctJointSignatures : Nat
    nonconstantEvenJointMultiplicity : Nat
    frickeAddsIndependentOperatorAtP11 : Bool

canonicalJointSpectrumBoundary : JointSpectrumBoundary
canonicalJointSpectrumBoundary = jointSpectrumBoundary true true true 3 3 false

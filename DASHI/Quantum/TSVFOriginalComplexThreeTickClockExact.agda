{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVFOriginalComplexThreeTickClockExact where

-- Selected discrete-clock extension of the ACTUAL original complex surface.
-- The original carrier, scalar, pairing, projectors and weight operations
-- are retained. X is a chosen nontrivial swap pulse, not a derived
-- spacetime clock, continuum generator or original empirical observer.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Quantum.TSVF as Q
import DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact as O
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as E
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C

data Clock : Set where
  early middle late : Clock

swap : E.ComplexPointerRecord → E.ComplexPointerRecord
swap (E.pointerRecord a b) = E.pointerRecord b a

swapTwice : ∀ v → swap (swap v) ≡ v
swapTwice (E.pointerRecord a b) = refl

swapPair : ∀ u v → E.hermitianPair (swap u) (swap v) ≡ E.hermitianPair u v
swapPair (E.pointerRecord (C.complex a b) (C.complex c d))
         (E.pointerRecord (C.complex e f) (C.complex g h)) =
  C.complexExt (Ring.solve-∀ a b c d e f g h)
               (Ring.solve-∀ a b c d e f g h)

frame : Clock → E.ComplexPointerRecord → E.ComplexPointerRecord
frame early v = swap v
frame middle v = v
frame late v = swap v

frameTwice : ∀ t v → frame t (frame t v) ≡ v
frameTwice early v = swapTwice v
frameTwice middle v = refl
frameTwice late v = swapTwice v

framePair : ∀ t u v → E.hermitianPair (frame t u) (frame t v) ≡ E.hermitianPair u v
framePair early u v = swapPair u v
framePair middle u v = refl
framePair late u v = swapPair u v

evolve : Clock → Clock → E.ComplexPointerRecord → E.ComplexPointerRecord
evolve from to v = frame to (frame from v)

evolveIdentity : ∀ t v → evolve t t v ≡ v
evolveIdentity = frameTwice

evolveCompose : ∀ a b c v → evolve b c (evolve a b v) ≡ evolve a c v
evolveCompose a b c v = cong (frame c) (frameTwice b (frame a v))

evolvePreservesPair : ∀ a b u v →
  E.hermitianPair (evolve a b u) (evolve a b v) ≡ E.hermitianPair u v
evolvePreservesPair a b u v
  rewrite framePair b (frame a u) (frame a v) | framePair a u v = refl

clockQuantum : Q.QuantumSurface
clockQuantum = record
  { Scalar = Q.QuantumSurface.Scalar O.finiteComplexQuantum
  ; Weight = Q.QuantumSurface.Weight O.finiteComplexQuantum
  ; Ket = E.ComplexPointerRecord
  ; Bra = E.ComplexPointerRecord
  ; Operator = Q.QuantumSurface.Operator O.finiteComplexQuantum
  ; Time = Clock
  ; evolveKet = evolve
  ; evolveBra = evolve
  ; apply = Q.QuantumSurface.apply O.finiteComplexQuantum
  ; pair = Q.QuantumSurface.pair O.finiteComplexQuantum
  ; normSquared = Q.QuantumSurface.normSquared O.finiteComplexQuantum
  ; divideWeight = Q.QuantumSurface.divideWeight O.finiteComplexQuantum
  ; Positive = Q.QuantumSurface.Positive O.finiteComplexQuantum
  }

-- Endpoint preparations are transported; fixed untransported endpoint
-- data need not preserve the original ABL probabilities.
liftEnsemble : Q.TSVFEnsemble O.finiteComplexQuantum → Q.TSVFEnsemble clockQuantum
liftEnsemble original = Q.prePostSelected early middle late
  (swap (Q.initialKet original)) (swap (Q.finalBra original))

originalForwardReopens : ∀ original →
  Q.forwardState (liftEnsemble original) ≡ Q.forwardState original
originalForwardReopens original = swapTwice (Q.initialKet original)

originalBackwardReopens : ∀ original →
  Q.backwardState (liftEnsemble original) ≡ Q.backwardState original
originalBackwardReopens original = swapTwice (Q.finalBra original)

originalEveryTransitionAmplitudeReopens :
  ∀ original (op : Q.QuantumSurface.Operator O.finiteComplexQuantum) →
  Q.transitionAmplitude (liftEnsemble original) op ≡ Q.transitionAmplitude original op
originalEveryTransitionAmplitudeReopens original op
  rewrite originalForwardReopens original | originalBackwardReopens original = refl

clockMeasurement : Q.ProjectiveMeasurement clockQuantum
clockMeasurement = record
  { Outcome = Q.ProjectiveMeasurement.Outcome O.finiteComplexMeasurement
  ; projector = Q.ProjectiveMeasurement.projector O.finiteComplexMeasurement
  ; totalPathWeight = λ ensemble →
      O.fraction
        (C.complexNormSq (Q.transitionAmplitude ensemble O.rightProjector)
         + C.complexNormSq (Q.transitionAmplitude ensemble O.wrongProjector))
        1ℚ
  }

originalTotalReopens : ∀ original →
  Q.ProjectiveMeasurement.totalPathWeight clockMeasurement (liftEnsemble original)
  ≡ Q.ProjectiveMeasurement.totalPathWeight O.finiteComplexMeasurement original
originalTotalReopens original
  rewrite originalEveryTransitionAmplitudeReopens original O.rightProjector
        | originalEveryTransitionAmplitudeReopens original O.wrongProjector = refl

liftContext : ∀ {original} →
  Q.ABLContext O.finiteComplexQuantum O.finiteComplexMeasurement original →
  Q.ABLContext clockQuantum clockMeasurement (liftEnsemble original)
liftContext {original} context = Q.ablContext proof
  where
  proof : Q.QuantumSurface.Positive clockQuantum
    (Q.ProjectiveMeasurement.totalPathWeight clockMeasurement (liftEnsemble original))
  proof rewrite originalTotalReopens original = Q.ABLContext.denominatorPositive context

originalABLReopens : ∀ {original}
  (context : Q.ABLContext O.finiteComplexQuantum O.finiteComplexMeasurement original)
  (outcome : Q.ProjectiveMeasurement.Outcome O.finiteComplexMeasurement) →
  Q.ablProbability (liftContext context) outcome ≡ Q.ablProbability context outcome
originalABLReopens {original} context outcome
  rewrite originalEveryTransitionAmplitudeReopens original
    (Q.ProjectiveMeasurement.projector O.finiteComplexMeasurement outcome)
        | originalTotalReopens original = refl

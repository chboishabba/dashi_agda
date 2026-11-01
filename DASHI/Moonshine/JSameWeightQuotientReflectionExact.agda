module DASHI.Moonshine.JSameWeightQuotientReflectionExact where

------------------------------------------------------------------------
-- REFLECTION / CONJUGATION OF THE SAME-WEIGHT J QUOTIENT
--
-- Existing owner:
--   JSameWeightQuotientInvariantExact
--
-- already proves modular weight cancellation for
--
--   j = E4^3 / Delta.
--
-- This module adds the orthogonal real-structure statement:
--
--   E4(r tau)    = conjugate(E4 tau)
--   Delta(r tau) = conjugate(Delta tau)
--
-- together with conjugation compatibility of cube and quotient imply
--
--   j(r tau) = conjugate(j tau).
--
-- If r tau = tau, then j(tau) is conjugation-fixed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Delta
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as J

record JReflectionAlgebra
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : Delta.DiscriminantAlgebra M)
    (Q : J.QuotientCancellationAlgebra M) : Set₁ where
  field
    reflectParameter :
      Eisenstein.Parameter M →
      Eisenstein.Parameter M

    conjugate :
      Eisenstein.Scalar M →
      Eisenstein.Scalar M

    e4Reflects :
      (tau : Eisenstein.Parameter M) →
      Delta.E4 M (reflectParameter tau)
      ≡
      conjugate (Delta.E4 M tau)

    discriminantReflects :
      (tau : Eisenstein.Parameter M) →
      Delta.unnormalisedDiscriminant M A (reflectParameter tau)
      ≡
      conjugate
        (Delta.unnormalisedDiscriminant M A tau)

    conjugateCube :
      (x : Eisenstein.Scalar M) →
      Delta.cube M (conjugate x)
      ≡
      conjugate (Delta.cube M x)

    conjugateQuotient :
      (numerator denominator : Eisenstein.Scalar M) →
      J._/ˢ_ Q
        (conjugate numerator)
        (conjugate denominator)
      ≡
      conjugate (J._/ˢ_ Q numerator denominator)

open JReflectionAlgebra public

jNumeratorReflects :
  ∀ {M A Q} →
  (R : JReflectionAlgebra M A Q) →
  (tau : Eisenstein.Parameter M) →
  J.jNumerator M (reflectParameter R tau)
  ≡
  conjugate R (J.jNumerator M tau)
jNumeratorReflects {M} R tau =
  trans
    (cong (Delta.cube M) (e4Reflects R tau))
    (conjugateCube R (Delta.E4 M tau))

jRatioReflects :
  ∀ {M A Q} →
  (R : JReflectionAlgebra M A Q) →
  (tau : Eisenstein.Parameter M) →
  J.jRatio M A Q (reflectParameter R tau)
  ≡
  conjugate R (J.jRatio M A Q tau)
jRatioReflects {M} {A} {Q} R tau =
  trans
    (cong₂ (J._/ˢ_ Q)
      (jNumeratorReflects R tau)
      (discriminantReflects R tau))
    (conjugateQuotient R
      (J.jNumerator M tau)
      (J.jDenominator M A tau))

record JReflectionFixedPoint
    {M : Eisenstein.EisensteinAnalyticModel}
    {A : Delta.DiscriminantAlgebra M}
    {Q : J.QuotientCancellationAlgebra M}
    (R : JReflectionAlgebra M A Q)
    (tau : Eisenstein.Parameter M) : Set where
  field
    fixed :
      reflectParameter R tau ≡ tau

open JReflectionFixedPoint public

jRatioConjugationFixed :
  ∀ {M A Q R tau} →
  JReflectionFixedPoint {M} {A} {Q} R tau →
  J.jRatio M A Q tau
  ≡
  conjugate R (J.jRatio M A Q tau)
jRatioConjugationFixed {M} {A} {Q} {R} {tau} F =
  trans
    (cong (J.jRatio M A Q) (sym (fixed F)))
    (jRatioReflects R tau)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record JReflectionBoundary : Set where
  constructor j-reflection-boundary
  field
    sameWeightModularCancellationOwnedElsewhere : Bool
    e4DeltaReflectionToJReflectionCompilerOwned : Bool
    fixedLocusJConjugationFixedCompilerOwned : Bool

    concreteComplexReflectionAlgebraInhabitedHere : Bool
    routeBLeanJReflectionTransportedIntoAgdaCarrier : Bool
    fixedLocusConjugationFixedInterpretedAsRealAxisHere : Bool

canonicalJReflectionBoundary : JReflectionBoundary
canonicalJReflectionBoundary =
  j-reflection-boundary
    true true true
    false false false

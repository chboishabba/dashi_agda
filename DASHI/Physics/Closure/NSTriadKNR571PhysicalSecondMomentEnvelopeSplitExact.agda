module DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentEnvelopeSplitExact where

------------------------------------------------------------------------
-- R571 GATE-A SPLIT: RADIAL TAYLOR ENVELOPES x STATE-DERIVATIVE ENVELOPES
--
-- The scoped Aug-5 compiler now states the correct finite-family theorem.  The
-- remaining physical work has two logically independent sources:
--
--   radial multiplier/Taylor side
--     |L|   <= |y|   A1
--     |R+|  <= |y|^2 A2
--     |R-|  <= |y|^2 A2
--
--   transported-state side
--     |g+ - g-| <= |y| G2
--     |g+|, |g-| <= G1.
--
-- This owner packages those two proof families separately and compiles their
-- product into the existing family-scoped PairedSecondMomentBudget.  It adds no
-- analytic estimate and no cutoff-uniformity theorem; it exists so the four
-- remaining proof leaves can be attacked independently (including in Lean)
-- without reopening the R571/R27/paired-Taylor plumbing.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNLuoScopedPairedSecondMomentBudgetExact as Scoped

record R571RadialTaylorEnvelope
    (family : List Moment.PairedSecondMomentSample) : Set₁ where
  field
    transportGradient transportCurvature : ℚ
    transportGradientNonnegative : 0ℚ ≤ transportGradient
    transportCurvatureNonnegative : 0ℚ ≤ transportCurvature

    linearIncrementBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ family →
      Moment.linearIncrement sample
      ≤ Moment.displacement sample * transportGradient

    plusRemainderBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ family →
      Moment.plusRemainder sample
      ≤ Moment.displacement sample * Moment.displacement sample
        * transportCurvature

    minusRemainderBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ family →
      Moment.minusRemainder sample
      ≤ Moment.displacement sample * Moment.displacement sample
        * transportCurvature

open R571RadialTaylorEnvelope public

record R571StateDerivativeEnvelope
    (family : List Moment.PairedSecondMomentSample) : Set₁ where
  field
    derivativeCurvature derivativeEnvelope : ℚ
    derivativeCurvatureNonnegative : 0ℚ ≤ derivativeCurvature
    derivativeEnvelopeNonnegative : 0ℚ ≤ derivativeEnvelope

    derivativeDifferenceBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ family →
      Moment.derivativeDifference sample
      ≤ Moment.displacement sample * derivativeCurvature

    plusDerivativeBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ family →
      Moment.plusDerivative sample ≤ derivativeEnvelope

    minusDerivativeBound :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ family →
      Moment.minusDerivative sample ≤ derivativeEnvelope

open R571StateDerivativeEnvelope public

record R571PhysicalSecondMomentEnvelopePackage : Set₁ where
  field
    family : List Moment.PairedSecondMomentSample
    radial : R571RadialTaylorEnvelope family
    state : R571StateDerivativeEnvelope family

open R571PhysicalSecondMomentEnvelopePackage public

compileScopedBudget :
  R571PhysicalSecondMomentEnvelopePackage →
  Scoped.ScopedPairedSecondMomentBudget
compileScopedBudget package = record
  { samples = family package
  ; transportGradient = transportGradient (radial package)
  ; derivativeCurvature = derivativeCurvature (state package)
  ; transportCurvature = transportCurvature (radial package)
  ; derivativeEnvelope = derivativeEnvelope (state package)
  ; transportGradientNonnegative =
      transportGradientNonnegative (radial package)
  ; derivativeCurvatureNonnegative =
      derivativeCurvatureNonnegative (state package)
  ; transportCurvatureNonnegative =
      transportCurvatureNonnegative (radial package)
  ; derivativeEnvelopeNonnegative =
      derivativeEnvelopeNonnegative (state package)
  ; linearIncrementBound = linearIncrementBound (radial package)
  ; derivativeDifferenceBound = derivativeDifferenceBound (state package)
  ; plusRemainderBound = plusRemainderBound (radial package)
  ; minusRemainderBound = minusRemainderBound (radial package)
  ; plusDerivativeBound = plusDerivativeBound (state package)
  ; minusDerivativeBound = minusDerivativeBound (state package)
  }

splitSecondMomentCoefficient :
  R571PhysicalSecondMomentEnvelopePackage → ℚ
splitSecondMomentCoefficient package =
  transportGradient (radial package) * derivativeCurvature (state package)
  + transportCurvature (radial package) * derivativeEnvelope (state package)
  + transportCurvature (radial package) * derivativeEnvelope (state package)

compiledCoefficientIsSplitCoefficient :
  (package : R571PhysicalSecondMomentEnvelopePackage) →
  Scoped.scopedSecondMomentCoefficient (compileScopedBudget package)
  ≡ splitSecondMomentCoefficient package
compiledCoefficientIsSplitCoefficient package = refl

compiledFiniteSecondMomentBound :
  (package : R571PhysicalSecondMomentEnvelopePackage) →
  Sum.sumBy (family package) Moment.pairedMagnitude
  ≤ splitSecondMomentCoefficient package
      * Sum.sumBy (family package) Moment.weightedSecondMoment
compiledFiniteSecondMomentBound package =
  Scoped.finiteScopedPairedSecondMomentBound (compileScopedBudget package)

r571PhysicalEnvelopeSplitCompilerClosed : Bool
r571PhysicalEnvelopeSplitCompilerClosed = true

r571RadialTaylorEnvelopeConstructedHere : Bool
r571RadialTaylorEnvelopeConstructedHere = false

r571StateDerivativeEnvelopeConstructedHere : Bool
r571StateDerivativeEnvelopeConstructedHere = false

r571ScopedEnvelopeSplitClosesUniformProducer : Bool
r571ScopedEnvelopeSplitClosesUniformProducer = false

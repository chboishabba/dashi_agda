module DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighLowDyadicGainExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Isolate the exact scale arithmetic behind the proposed high--high to low
-- backscatter gain.  If the output derivative costs lambda_q while the two
-- inputs live at lambda_{q+d}, the dimensionless ratio is
--
--   lambda_q / lambda_{q+d} = 2^-d.
--
-- On the repository's rational dyadic carrier this is proved without
-- division by showing
--
--   2^-d * lambda_{q+d} = lambda_q.
--
-- The geometric gains sum to at most two over every finite gap prefix.  The
-- actual bilinear Fourier-support estimate producing this ratio remains a
-- separate continuum theorem and is not asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _-_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; subst)
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Obstruction

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

highInputScale : Nat → Nat → ℚ
highInputScale outputShell gap =
  Scale.dyadicScale outputShell * Scale.dyadicScale gap

highHighLowGain : Nat → ℚ
highHighLowGain = Near.windowRoot

highHighLowGainCalibration :
  (outputShell gap : Nat) →
  highHighLowGain gap * highInputScale outputShell gap
  ≡ Scale.dyadicScale outputShell
highHighLowGainCalibration outputShell gap =
  begin
    highHighLowGain gap * highInputScale outputShell gap
  ≡⟨ solve
       ( Near.windowRoot gap
       ∷ Scale.dyadicScale outputShell
       ∷ Scale.dyadicScale gap
       ∷ []) ⟩
    Scale.dyadicScale outputShell
      * (Near.windowRoot gap * Scale.dyadicScale gap)
  ≡⟨ cong
       (Scale.dyadicScale outputShell *_)
       (Obstruction.reciprocalDyadicIdentity gap) ⟩
    Scale.dyadicScale outputShell * 1ℚ
  ≡⟨ solve (Scale.dyadicScale outputShell ∷ []) ⟩
    Scale.dyadicScale outputShell
  ∎

highHighLowGainPrefix : Nat → ℚ
highHighLowGainPrefix cutoff = Geo.partialSum half cutoff

halfNonnegative : 0ℚ ≤ half
halfNonnegative = toWitness {a? = 0ℚ ≤? half} _

oneMinusHalfPositive : 0ℚ < 1ℚ - half
oneMinusHalfPositive = toWitness {a? = 0ℚ <? 1ℚ - half} _

halfBoundIdentity :
  (1ℚ - half) * two ≡ 1ℚ
halfBoundIdentity = solve []

highHighLowGainPrefixBound :
  (cutoff : Nat) →
  highHighLowGainPrefix cutoff ≤ two
highHighLowGainPrefixBound cutoff =
  Geo.geometricPartialSumBound
    half two cutoff
    halfNonnegative oneMinusHalfPositive halfBoundIdentity

weightedHighHighLowPrefix : ℚ → Nat → ℚ
weightedHighHighLowPrefix base cutoff =
  base * highHighLowGainPrefix cutoff

weightedHighHighLowPrefixBound :
  (base : ℚ) →
  0ℚ ≤ base →
  (cutoff : Nat) →
  weightedHighHighLowPrefix base cutoff ≤ two * base
weightedHighHighLowPrefixBound base baseNonnegative cutoff =
  let
    instance
      baseIsNonnegative = nonNegative baseNonnegative

    scaled :
      base * highHighLowGainPrefix cutoff ≤ base * two
    scaled =
      ℚₚ.*-monoˡ-≤-nonNeg
        base
        (highHighLowGainPrefixBound cutoff)

    targetMeaning : base * two ≡ two * base
    targetMeaning = solve (base ∷ [])
  in
  subst
    (λ upper → weightedHighHighLowPrefix base cutoff ≤ upper)
    targetMeaning
    scaled

module DASHI.Physics.Closure.NSTriadKNLuoSchurEnvelopeRefinementExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Make the canonical (1/4)^j (1/32)^d kernel an upper envelope rather than a
-- sacred physical identity.  A physical estimate may naturally produce any
-- stronger intermediate low-shell and gap profiles.  If those profiles are
-- pointwise below the canonical powers, this module constructs the existing
-- finite dyadic multiplier profile and therefore inherits the checked Schur
-- summation theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierMagnitudeExact as Dyadic

record RefinedDyadicEnvelope : Set where
  constructor refined-dyadic-envelope
  field
    actualLow actualGap : Nat → ℚ
    intermediateLow intermediateGap : Nat → ℚ
    lowGradient : ℚ

    actualLowNonnegative :
      (lowShell : Nat) → 0ℚ ≤ actualLow lowShell
    actualGapNonnegative :
      (gap : Nat) → 0ℚ ≤ actualGap gap
    lowGradientNonnegative : 0ℚ ≤ lowGradient

    actualLowBelowIntermediate :
      (lowShell : Nat) →
      actualLow lowShell ≤ intermediateLow lowShell

    intermediateLowBelowCanonical :
      (lowShell : Nat) →
      intermediateLow lowShell ≤ Geo.pow Geo.quarter lowShell

    actualGapBelowIntermediate :
      (gap : Nat) →
      actualGap gap ≤ intermediateGap gap

    intermediateGapBelowCanonical :
      (gap : Nat) →
      intermediateGap gap ≤ Geo.pow Geo.thirtySecond gap

open RefinedDyadicEnvelope public

actualLowBelowCanonical :
  (envelope : RefinedDyadicEnvelope) →
  (lowShell : Nat) →
  actualLow envelope lowShell ≤ Geo.pow Geo.quarter lowShell
actualLowBelowCanonical envelope lowShell =
  ℚₚ.≤-trans
    (actualLowBelowIntermediate envelope lowShell)
    (intermediateLowBelowCanonical envelope lowShell)

actualGapBelowCanonical :
  (envelope : RefinedDyadicEnvelope) →
  (gap : Nat) →
  actualGap envelope gap ≤ Geo.pow Geo.thirtySecond gap
actualGapBelowCanonical envelope gap =
  ℚₚ.≤-trans
    (actualGapBelowIntermediate envelope gap)
    (intermediateGapBelowCanonical envelope gap)

refinedEnvelopeAsCanonicalProfile :
  RefinedDyadicEnvelope → Dyadic.FiniteDyadicMultiplierProfile
refinedEnvelopeAsCanonicalProfile envelope =
  Dyadic.finite-dyadic-multiplier
    (actualLow envelope)
    (actualGap envelope)
    (lowGradient envelope)
    (actualLowNonnegative envelope)
    (actualGapNonnegative envelope)
    (lowGradientNonnegative envelope)
    (actualLowBelowCanonical envelope)
    (actualGapBelowCanonical envelope)

refinedMultiplierMagnitudeBound :
  (envelope : RefinedDyadicEnvelope) →
  (lowShell gap : Nat) →
  Dyadic.multiplierMagnitude
    (refinedEnvelopeAsCanonicalProfile envelope)
    lowShell gap
  ≤ Geo.pow Geo.quarter lowShell
      * Geo.pow Geo.thirtySecond gap
      * lowGradient envelope
refinedMultiplierMagnitudeBound envelope =
  Dyadic.multiplierMagnitudeBound
    (refinedEnvelopeAsCanonicalProfile envelope)

schurEnvelopeRefinementClosed : Bool
schurEnvelopeRefinementClosed = true

canonicalKernelIsUpperEnvelopeNotPhysicalIdentity : Bool
canonicalKernelIsUpperEnvelopeNotPhysicalIdentity = true

schurEnvelopeRefinementClosedIsTrue :
  schurEnvelopeRefinementClosed ≡ true
schurEnvelopeRefinementClosedIsTrue = refl

canonicalKernelIsUpperEnvelopeNotPhysicalIdentityIsTrue :
  canonicalKernelIsUpperEnvelopeNotPhysicalIdentity ≡ true
canonicalKernelIsUpperEnvelopeNotPhysicalIdentityIsTrue = refl

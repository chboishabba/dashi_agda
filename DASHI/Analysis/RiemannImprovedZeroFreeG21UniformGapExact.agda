module DASHI.Analysis.RiemannImprovedZeroFreeG21UniformGapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannImprovedZeroFreeHalfPlaneDonorExact as Donor

------------------------------------------------------------------------
-- Quantitative consequence for the live G21 height geometry.
--
-- G21's pole height is p = 1/2 and its off-line height is a = |alpha|.
-- Once the external same-zeta donor is attached, the conservative cap is
--
--   a <= 187479/500000.
--
-- Therefore the pole/off-line separation has the uniform lower bound
--
--   p-a >= (250000-187479)/500000
--       = 62521/500000
--       = 0.125042
--       > 1/8.
--
-- This is substantially more useful for G21 than the raw ~4.2e-5 strip
-- contraction: the old strict-strip input gave only a < p and therefore no
-- uniform positive lower bound on p-a.  A uniform gap can feed future compact
-- Taylor-remainder and determinant-margin estimates.  It still does not prove
-- either actual parity minor or pole-quotient transversality.
------------------------------------------------------------------------

safeDenominator : Nat
safeDenominator = Donor.safeDenominator

safeAlphaNumerator : Nat
safeAlphaNumerator = Donor.safeAlphaNumerator

halfNumerator : Nat
halfNumerator = 250000

safePoleGapNumerator : Nat
safePoleGapNumerator = 62521

safeAlphaPlusPoleGapIsHalf :
  safeAlphaNumerator + safePoleGapNumerator ≡ halfNumerator
safeAlphaPlusPoleGapIsHalf = refl

safePoleGapStrictlyExceedsOneEighthCrossProduct :
  8 * safePoleGapNumerator ≡ safeDenominator + 168
safePoleGapStrictlyExceedsOneEighthCrossProduct = refl

------------------------------------------------------------------------
-- Least-privilege consumer interface.
--
-- The ordered subtraction lives on the future concrete G21 height carrier.
-- We expose exactly the theorem shape needed by quantitative minor/Taylor
-- consumers rather than pretending Nat numerator arithmetic supplies that
-- cross-carrier theorem by itself.
------------------------------------------------------------------------

record G21UniformPoleGapAttachment : Set₁ where
  field
    Height : Set
    poleHeight : Height
    offLineHeight : Height
    gapLowerBound : Height
    GapAtLeast : Height → Height → Height → Set

    samePoleHeightAsG21 : Set
    samePoleHeightAsG21Receipt : samePoleHeightAsG21

    sameOffLineHeightAsG21 : Set
    sameOffLineHeightAsG21Receipt : sameOffLineHeightAsG21

    gapLowerBoundRepresents62521Over500000 : Set
    gapLowerBoundRepresents62521Over500000Receipt :
      gapLowerBoundRepresents62521Over500000

    uniformPoleGap : GapAtLeast poleHeight offLineHeight gapLowerBound

open G21UniformPoleGapAttachment public

record G21UniformPoleGapBoundary : Set where
  constructor g21-uniform-pole-gap-boundary
  field
    donorTurnsStrictSeparationIntoUniformMargin : Bool
    donorTurnsStrictSeparationIntoUniformMarginIsTrue :
      donorTurnsStrictSeparationIntoUniformMargin ≡ true

    uniformPositivePoleGapCompilerConstructed : Bool
    uniformPositivePoleGapCompilerConstructedIsTrue :
      uniformPositivePoleGapCompilerConstructed ≡ true

    rationalGapStrictlyExceedsOneEighth : Bool
    rationalGapStrictlyExceedsOneEighthIsTrue :
      rationalGapStrictlyExceedsOneEighth ≡ true

    taylorRemainderBoundDerived : Bool
    taylorRemainderBoundDerivedIsFalse : taylorRemainderBoundDerived ≡ false

    actualParityMinorDerived : Bool
    actualParityMinorDerivedIsFalse : actualParityMinorDerived ≡ false

    poleQuotientTransversalityDerived : Bool
    poleQuotientTransversalityDerivedIsFalse :
      poleQuotientTransversalityDerived ≡ false

    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

    highestAlphaReading : String

canonicalG21UniformPoleGapBoundary : G21UniformPoleGapBoundary
canonicalG21UniformPoleGapBoundary =
  g21-uniform-pole-gap-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Conditional on exact same-zeta transport of the pinned Liu/OpenAI zero-free theorem, G21 improves from qualitative 0<a<p=1/2 to the uniform quantitative separation p-a >= 62521/500000 > 1/8. The Nat arithmetic is exact here; the ordered same-height carrier attachment remains proof-relevant. This creates a compact quantitative domain for future Taylor/remainder and determinant-margin attacks but does not itself prove sinh/cosh TP2, an actual parity minor, pole-quotient transversality, or RH."

module DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact where

------------------------------------------------------------------------
-- PRIME REPRESENTATION / CODEC ADMISSIBILITY / ALGEBRAIC DEFECT ARE DISTINCT
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Moonshine.QuadraticIrrationalSignedApproximationFibreExact as Quad

------------------------------------------------------------------------
-- 1. A rational representation fibre is a signed prime-valuation word.
--
-- We deliberately permit a residual prime tail.  SSP/Monster primes can act as
-- a privileged dictionary/compression basis without claiming that every good
-- approximation factors only through the canonical SSP set.
------------------------------------------------------------------------

record PrimeExponent : Set where
  constructor primeExponent
  field
    prime : Nat
    exponent : SSP.SignedMultiplicity

record PrimeCompressionFibre : Set where
  constructor prime-compression-fibre
  field
    dictionaryPart : List PrimeExponent
    residualPart : List PrimeExponent

-- Exact factorisation of 34641/40000 at the prime-valuation level:
--   34641 = 3^3 * 1283
--   40000 = 2^6 * 5^4
-- The numeric product equalities are kept as machine-checkable witnesses.
decimalNumeratorFactorisation : 34641 ≡ 27 * 1283
decimalNumeratorFactorisation = refl

decimalDenominatorFactorisation : 40000 ≡ 64 * 625
decimalDenominatorFactorisation = refl

decimalCodecPrimeFibre : PrimeCompressionFibre
decimalCodecPrimeFibre =
  prime-compression-fibre
    (primeExponent 2 (SSP.negativeMultiplicity 6) ∷
     primeExponent 3 (SSP.positiveMultiplicity 3) ∷
     primeExponent 5 (SSP.negativeMultiplicity 4) ∷
     [])
    (primeExponent 1283 (SSP.positiveMultiplicity 1) ∷ [])

------------------------------------------------------------------------
-- 2. Codec admissibility is a consumer constraint, not semantic equality.
------------------------------------------------------------------------

data CodecClass : Set where
  terminatingDecimalCodec : CodecClass
  unrestrictedRationalCodec : CodecClass
  sspDictionaryWithResidualCodec : CodecClass

record CodecAdmissibility : Set where
  constructor codec-admissibility
  field
    codec : CodecClass
    numerator : Nat
    denominator : Nat
    representation : PrimeCompressionFibre

canonicalDecimalAdmissibility : CodecAdmissibility
canonicalDecimalAdmissibility =
  codec-admissibility terminatingDecimalCodec 34641 40000 decimalCodecPrimeFibre

------------------------------------------------------------------------
-- 3. BIDI split: compression says HOW p/q is encoded; quadratic defect says
--    WHERE that encoded rational lies relative to the algebraic target.
------------------------------------------------------------------------

record ApproximationCodecState : Set where
  constructor approximation-codec-state
  field
    admissibility : CodecAdmissibility
    direction : Triadic.KernelTrit

canonicalDecimalApproximationCodecState : ApproximationCodecState
canonicalDecimalApproximationCodecState =
  approximation-codec-state
    canonicalDecimalAdmissibility
    (Quad.sqrtThreeHalfTrit Quad.decimal866025Defect)

canonicalDecimalDirectionIsConverging :
  ApproximationCodecState.direction canonicalDecimalApproximationCodecState
  ≡ Triadic.negativeTrit
canonicalDecimalDirectionIsConverging = refl

------------------------------------------------------------------------
-- 4. Two-state nonzero boundary versus balanced ternary centre.
--
-- The Pell fibres around sqrt(3)/2 have two realised nonzero direction states
-- (- and +), while 0 is the exact algebraic centre.  The binary boundary is
-- therefore the strict-nonzero subcarrier of the balanced trit, not an
-- arithmetic claim that the integer defects -3 and +1 literally sum to +2.
------------------------------------------------------------------------

data StrictSignedSide : Set where
  lowerSide : StrictSignedSide
  upperSide : StrictSignedSide

strictSideToTrit : StrictSignedSide → Triadic.KernelTrit
strictSideToTrit lowerSide = Triadic.negativeTrit
strictSideToTrit upperSide = Triadic.positiveTrit

strictSidesDistinctFromCentre :
  (strictSideToTrit lowerSide ≡ Triadic.negativeTrit) ×
  (strictSideToTrit upperSide ≡ Triadic.positiveTrit)
strictSidesDistinctFromCentre = refl , refl

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

data PrimeCompressionResidual : Set where
  missingGeneralPrimeFactorisationProducer : PrimeCompressionResidual
  missingSSPDictionaryCostModel : PrimeCompressionResidual
  missingCodecConstrainedBestApproximationTheorem : PrimeCompressionResidual
  missingWaveCarrierAdmissibilityLift : PrimeCompressionResidual

record PrimeCompressionBidiFrontier : Set where
  constructor prime-compression-bidi-frontier
  field
    signedPrimeRepresentationExactForDecimal : Bool
    residualPrimeTailPermitted : Bool
    approximationDirectionSeparate : Bool
    binaryBoundaryIsStrictNonzeroTrit : Bool
    universalSSPOptimalityClaimed : Bool
    firstResidual : PrimeCompressionResidual

canonicalPrimeCompressionBidiFrontier : PrimeCompressionBidiFrontier
canonicalPrimeCompressionBidiFrontier =
  prime-compression-bidi-frontier
    true true true true false
    missingGeneralPrimeFactorisationProducer

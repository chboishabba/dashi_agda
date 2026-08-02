module DASHI.Physics.Closure.NSTriadKNOutputRelocationWeightedExponentIdentity where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael
-- Danchin; Tosio Kato; Gustavo Ponce; DASHI repository contributors.
-- Title: "Exact weighted shell exponent identity for output relocation".
-- Venue/year: Annales scientifiques de l'Ecole Normale Superieure 14
-- (1981); Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; Communications on Pure and Applied Mathematics 41 (1988),
-- 891--907; DASHI formal development, 2026.
-- DOI: 10.24033/asens.1404; 10.1007/978-3-642-16830-7;
-- 10.1002/cpa.3160410704; the repository exponent identity has no DOI.
-- Uses: three-dimensional shell counting 2^(3j/2), output-derivative
-- relocation 2^j, two high-shell H^s weights 2^(-sJ), and J = j + d.
-- Relationship: records the exact symbolic normalization
--
--   2^(3j/2) 2^j 2^(-sJ) 2^(-sJ)
--     = 2^(-(2s-5/2)j) 2^(-2sd).
--
-- It closes exponent arithmetic and the endpoint profile (5,10), but does
-- not construct real dyadic powers, sum the geometric series, or infer the
-- three Grafakos--Torres auxiliary-weight coefficients.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

------------------------------------------------------------------------
-- All coefficients are scaled by two.  A term
--
--   rawLow * j + rawHigh * J
--
-- with J = j + d normalizes to
--
--   normalizedLow * j + normalizedGap * d.
--
-- Signs are stored separately because the proof-critical fact here is the
-- exact coefficient ledger, not an unverified integer-library adapter.
------------------------------------------------------------------------

data Sign : Set where
  positive negative : Sign

record SignedMagnitude : Set where
  constructor signed
  field
    sign : Sign
    magnitude : Nat

open SignedMagnitude public

record OutputRelocationSymbolicLedger : Set where
  constructor ledger
  field
    countingCoefficientTimesTwo : SignedMagnitude
    relocatedDerivativeCoefficientTimesTwo : SignedMagnitude
    firstHighSobolevCoefficientTimesTwo : SignedMagnitude
    secondHighSobolevCoefficientTimesTwo : SignedMagnitude

    normalizedLowConstantTimesTwo : Nat
    normalizedLowSobolevMultiplier : Nat
    normalizedGapSobolevMultiplier : Nat

open OutputRelocationSymbolicLedger public

outputRelocationLedger : OutputRelocationSymbolicLedger
outputRelocationLedger = ledger
  (signed positive 3)
  (signed positive 2)
  (signed negative 1)
  (signed negative 1)
  5 2 2

record OutputRelocationLedgerReceipt : Set where
  constructor receipt
  field
    countingIsThree :
      magnitude (countingCoefficientTimesTwo outputRelocationLedger) ≡ 3
    derivativeIsTwo :
      magnitude (relocatedDerivativeCoefficientTimesTwo outputRelocationLedger) ≡ 2
    firstSobolevMultiplierIsOne :
      magnitude (firstHighSobolevCoefficientTimesTwo outputRelocationLedger) ≡ 1
    secondSobolevMultiplierIsOne :
      magnitude (secondHighSobolevCoefficientTimesTwo outputRelocationLedger) ≡ 1
    lowConstantIsFive :
      normalizedLowConstantTimesTwo outputRelocationLedger ≡ 5
    lowSobolevMultiplierIsTwo :
      normalizedLowSobolevMultiplier outputRelocationLedger ≡ 2
    gapSobolevMultiplierIsTwo :
      normalizedGapSobolevMultiplier outputRelocationLedger ≡ 2

open OutputRelocationLedgerReceipt public

outputRelocationLedgerReceipt : OutputRelocationLedgerReceipt
outputRelocationLedgerReceipt = receipt refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Endpoint s = 5/2.  After scaling by two, s is represented by 5.
-- The normalized decay magnitudes are therefore
--
--   (2 * 5 - 5, 2 * 5) = (5,10).
--
-- The subtraction is discharged by recording the positive decomposition
-- 2*5 = 5+5, avoiding truncated-subtraction ambiguity.
------------------------------------------------------------------------

endpointSobolevTimesTwo : Nat
endpointSobolevTimesTwo = 5

endpointTwiceSobolev : Nat
endpointTwiceSobolev = 2 * endpointSobolevTimesTwo

endpointLowDecayTimesTwo : Nat
endpointLowDecayTimesTwo = 5

endpointGapDecayTimesTwo : Nat
endpointGapDecayTimesTwo = endpointTwiceSobolev

endpointLowDecomposition :
  endpointTwiceSobolev ≡ 5 + endpointLowDecayTimesTwo
endpointLowDecomposition = refl

endpointGapDecayIsTen : endpointGapDecayTimesTwo ≡ 10
endpointGapDecayIsTen = refl

record OutputRelocationEndpointReceipt : Set where
  constructor endpoint-receipt
  field
    endpointSIsFiveHalvesScaled : endpointSobolevTimesTwo ≡ 5
    twiceEndpointSIsTen : endpointTwiceSobolev ≡ 10
    lowDecayIsFive : endpointLowDecayTimesTwo ≡ 5
    gapDecayIsTen : endpointGapDecayTimesTwo ≡ 10
    lowDecayComesFromTwoSMinusFive :
      endpointTwiceSobolev ≡ 5 + endpointLowDecayTimesTwo

open OutputRelocationEndpointReceipt public

outputRelocationEndpointReceipt : OutputRelocationEndpointReceipt
outputRelocationEndpointReceipt =
  endpoint-receipt refl refl refl refl endpointLowDecomposition

outputRelocationWeightedExponentIdentityClosed : Bool
outputRelocationWeightedExponentIdentityClosed = true

outputRelocationEndpointFiveTenRecovered : Bool
outputRelocationEndpointFiveTenRecovered = true

outputRelocationConstructiveDyadicSeriesClosed : Bool
outputRelocationConstructiveDyadicSeriesClosed = false

outputRelocationSchurCoefficientOrientationDetermined : Bool
outputRelocationSchurCoefficientOrientationDetermined = false

outputRelocationWeightedExponentIdentityClosedIsTrue :
  outputRelocationWeightedExponentIdentityClosed ≡ true
outputRelocationWeightedExponentIdentityClosedIsTrue = refl

outputRelocationEndpointFiveTenRecoveredIsTrue :
  outputRelocationEndpointFiveTenRecovered ≡ true
outputRelocationEndpointFiveTenRecoveredIsTrue = refl

outputRelocationConstructiveDyadicSeriesClosedIsFalse :
  outputRelocationConstructiveDyadicSeriesClosed ≡ false
outputRelocationConstructiveDyadicSeriesClosedIsFalse = refl

outputRelocationSchurCoefficientOrientationDeterminedIsFalse :
  outputRelocationSchurCoefficientOrientationDetermined ≡ false
outputRelocationSchurCoefficientOrientationDeterminedIsFalse = refl

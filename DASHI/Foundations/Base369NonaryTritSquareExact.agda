module DASHI.Foundations.Base369NonaryTritSquareExact where

------------------------------------------------------------------------
-- Exact finite carrier theorem:
--
--   Fin 9  ~=  Trit x Trit
--
-- The equality is at carrier/address level.  It does not identify Z/9Z with
-- F_3^2 as a group or ring.  The low trit is the residue modulo three; additive
-- complement modulo nine fixes its neutral fibre and reverses its polarity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( NonaryTruth
  ; non-0; non-1; non-2; non-3; non-4
  ; non-5; non-6; non-7; non-8
  )

open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne
  ; sspZero
  ; sspPosOne
  )

record TritSquare : Set where
  constructor tritSquare
  field
    highTrit : SSPTrit
    lowTrit : SSPTrit

open TritSquare public

nonaryDigitToTritSquare : NonaryTruth → TritSquare
nonaryDigitToTritSquare non-0 = tritSquare sspZero sspZero
nonaryDigitToTritSquare non-1 = tritSquare sspZero sspPosOne
nonaryDigitToTritSquare non-2 = tritSquare sspZero sspNegOne
nonaryDigitToTritSquare non-3 = tritSquare sspPosOne sspZero
nonaryDigitToTritSquare non-4 = tritSquare sspPosOne sspPosOne
nonaryDigitToTritSquare non-5 = tritSquare sspPosOne sspNegOne
nonaryDigitToTritSquare non-6 = tritSquare sspNegOne sspZero
nonaryDigitToTritSquare non-7 = tritSquare sspNegOne sspPosOne
nonaryDigitToTritSquare non-8 = tritSquare sspNegOne sspNegOne

tritSquareToNonaryDigit : TritSquare → NonaryTruth
tritSquareToNonaryDigit (tritSquare sspZero sspZero) = non-0
tritSquareToNonaryDigit (tritSquare sspZero sspPosOne) = non-1
tritSquareToNonaryDigit (tritSquare sspZero sspNegOne) = non-2
tritSquareToNonaryDigit (tritSquare sspPosOne sspZero) = non-3
tritSquareToNonaryDigit (tritSquare sspPosOne sspPosOne) = non-4
tritSquareToNonaryDigit (tritSquare sspPosOne sspNegOne) = non-5
tritSquareToNonaryDigit (tritSquare sspNegOne sspZero) = non-6
tritSquareToNonaryDigit (tritSquare sspNegOne sspPosOne) = non-7
tritSquareToNonaryDigit (tritSquare sspNegOne sspNegOne) = non-8

nonaryDigitRoundTrip :
  (digit : NonaryTruth) →
  tritSquareToNonaryDigit (nonaryDigitToTritSquare digit) ≡ digit
nonaryDigitRoundTrip non-0 = refl
nonaryDigitRoundTrip non-1 = refl
nonaryDigitRoundTrip non-2 = refl
nonaryDigitRoundTrip non-3 = refl
nonaryDigitRoundTrip non-4 = refl
nonaryDigitRoundTrip non-5 = refl
nonaryDigitRoundTrip non-6 = refl
nonaryDigitRoundTrip non-7 = refl
nonaryDigitRoundTrip non-8 = refl

tritSquareRoundTrip :
  (square : TritSquare) →
  nonaryDigitToTritSquare (tritSquareToNonaryDigit square) ≡ square
tritSquareRoundTrip (tritSquare sspZero sspZero) = refl
tritSquareRoundTrip (tritSquare sspZero sspPosOne) = refl
tritSquareRoundTrip (tritSquare sspZero sspNegOne) = refl
tritSquareRoundTrip (tritSquare sspPosOne sspZero) = refl
tritSquareRoundTrip (tritSquare sspPosOne sspPosOne) = refl
tritSquareRoundTrip (tritSquare sspPosOne sspNegOne) = refl
tritSquareRoundTrip (tritSquare sspNegOne sspZero) = refl
tritSquareRoundTrip (tritSquare sspNegOne sspPosOne) = refl
tritSquareRoundTrip (tritSquare sspNegOne sspNegOne) = refl

nonaryDigitToHighTrit : NonaryTruth → SSPTrit
nonaryDigitToHighTrit digit = highTrit (nonaryDigitToTritSquare digit)

nonaryDigitToLowTrit : NonaryTruth → SSPTrit
nonaryDigitToLowTrit digit = lowTrit (nonaryDigitToTritSquare digit)

negateSSPTrit : SSPTrit → SSPTrit
negateSSPTrit sspNegOne = sspPosOne
negateSSPTrit sspZero = sspZero
negateSSPTrit sspPosOne = sspNegOne

negateSSPTritInvolutive :
  (trit : SSPTrit) →
  negateSSPTrit (negateSSPTrit trit) ≡ trit
negateSSPTritInvolutive sspNegOne = refl
negateSSPTritInvolutive sspZero = refl
negateSSPTritInvolutive sspPosOne = refl

complementNonaryDigit : NonaryTruth → NonaryTruth
complementNonaryDigit non-0 = non-0
complementNonaryDigit non-1 = non-8
complementNonaryDigit non-2 = non-7
complementNonaryDigit non-3 = non-6
complementNonaryDigit non-4 = non-5
complementNonaryDigit non-5 = non-4
complementNonaryDigit non-6 = non-3
complementNonaryDigit non-7 = non-2
complementNonaryDigit non-8 = non-1

complementNonaryDigitInvolutive :
  (digit : NonaryTruth) →
  complementNonaryDigit (complementNonaryDigit digit) ≡ digit
complementNonaryDigitInvolutive non-0 = refl
complementNonaryDigitInvolutive non-1 = refl
complementNonaryDigitInvolutive non-2 = refl
complementNonaryDigitInvolutive non-3 = refl
complementNonaryDigitInvolutive non-4 = refl
complementNonaryDigitInvolutive non-5 = refl
complementNonaryDigitInvolutive non-6 = refl
complementNonaryDigitInvolutive non-7 = refl
complementNonaryDigitInvolutive non-8 = refl

complementReversesLowTrit :
  (digit : NonaryTruth) →
  nonaryDigitToLowTrit (complementNonaryDigit digit)
  ≡ negateSSPTrit (nonaryDigitToLowTrit digit)
complementReversesLowTrit non-0 = refl
complementReversesLowTrit non-1 = refl
complementReversesLowTrit non-2 = refl
complementReversesLowTrit non-3 = refl
complementReversesLowTrit non-4 = refl
complementReversesLowTrit non-5 = refl
complementReversesLowTrit non-6 = refl
complementReversesLowTrit non-7 = refl
complementReversesLowTrit non-8 = refl

data LowTritFibre : Set where
  neutralLowFibre
  positiveLowFibre
  negativeLowFibre : LowTritFibre

lowTritFibre : NonaryTruth → LowTritFibre
lowTritFibre non-0 = neutralLowFibre
lowTritFibre non-1 = positiveLowFibre
lowTritFibre non-2 = negativeLowFibre
lowTritFibre non-3 = neutralLowFibre
lowTritFibre non-4 = positiveLowFibre
lowTritFibre non-5 = negativeLowFibre
lowTritFibre non-6 = neutralLowFibre
lowTritFibre non-7 = positiveLowFibre
lowTritFibre non-8 = negativeLowFibre

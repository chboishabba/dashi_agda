module DASHI.Physics.Closure.NSTriadKNPhysicalTriadExchangeCharacterRound73Exact where

------------------------------------------------------------------------
-- ROUND73 / EXCHANGE CHARACTER BEFORE MAJORIZATION
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Pierre Serre.
-- Title: "Linear Representations of Finite Groups".
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Author: Jean-Michel Bony.
-- DOI: 10.24033/asens.1404.
--
-- Cross-pollination: the recent finite-character work in the repository uses
-- exact character projection before interval/absolute-value loss.  The relevant
-- NS symmetry is not C3: on an ordered resonant pair it is the C2 exchange
--
--     (p,q) <-> (q,p).
--
-- This file proves the finite algebra needed downstream: every exchange-odd
-- pair cancels exactly before any absolute value or Gram bound is applied.
-- It does NOT assert that a physical HH/CC coefficient is exchange odd; that
-- same-object PDE theorem remains explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_)
import Data.Rational.Properties as ℚP

data ExchangeSector : Set where
  exchangeEven exchangeOdd : ExchangeSector

record ExchangePair : Set where
  constructor exchange-pair
  field
    forward : ℚ
    reversed : ℚ
    sector : ExchangeSector

open ExchangePair public

pairSum : ExchangePair → ℚ
pairSum p = forward p + reversed p

record CertifiedExchangeOdd (p : ExchangePair) : Set where
  field
    isOddSector : sector p ≡ exchangeOdd
    reversedIsNegative : reversed p ≡ - forward p

open CertifiedExchangeOdd public

exchangeOddPairCancels :
  ∀ {p} → CertifiedExchangeOdd p → pairSum p ≡ 0ℚ
exchangeOddPairCancels {p} witness
  rewrite reversedIsNegative witness = ℚP.+-inverseʳ (forward p)

oddPairSum : List ExchangePair → ℚ
oddPairSum [] = 0ℚ
oddPairSum (p ∷ rest) = pairSum p + oddPairSum rest

-- The recursive carrier deliberately certifies only those physical pair rows
-- for which the source theorem proves exchange-odd covariance.
data ExchangeOddFamily : List ExchangePair → Set where
  odd[] : ExchangeOddFamily []
  odd∷ : ∀ {p rest} → CertifiedExchangeOdd p →
    ExchangeOddFamily rest → ExchangeOddFamily (p ∷ rest)

exchangeOddFamilyCancels :
  ∀ {pairs} → ExchangeOddFamily pairs → oddPairSum pairs ≡ 0ℚ
exchangeOddFamilyCancels odd[] = refl
exchangeOddFamilyCancels (odd∷ {p} witness rest)
  rewrite exchangeOddPairCancels witness
        | exchangeOddFamilyCancels rest = refl

round73ExchangeCharacterCancellationConstructed : Bool
round73ExchangeCharacterCancellationConstructed = true

round73PhysicalHHCCExchangeSectorIdentificationConstructed : Bool
round73PhysicalHHCCExchangeSectorIdentificationConstructed = false

round73ExchangeCharacterCancellationConstructedIsTrue :
  round73ExchangeCharacterCancellationConstructed ≡ true
round73ExchangeCharacterCancellationConstructedIsTrue = refl

round73PhysicalHHCCExchangeSectorIdentificationConstructedIsFalse :
  round73PhysicalHHCCExchangeSectorIdentificationConstructed ≡ false
round73PhysicalHHCCExchangeSectorIdentificationConstructedIsFalse = refl

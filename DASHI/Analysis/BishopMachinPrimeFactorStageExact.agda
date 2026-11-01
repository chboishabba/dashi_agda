module DASHI.Analysis.BishopMachinPrimeFactorStageExact where

------------------------------------------------------------------------
-- K04c: PROOF-CARRYING FACTORISATION OF EVERY RATIONAL MACHIN STAGE.
--
-- Original owner: Data.Nat.Primality.Factorisation.factorise (Agda stdlib).
-- Reuse of DASHI.Moonshine.AristotleHeckeGeneralPrimePowerDecompositionExact
--   .canonicalRawPrimeFactorisation, and earlier
--   QuadraticApproximationPrimeCompressionBidiExact / SignedSSP... .
-- John Machin (1706); Murray (2022), arXiv:2205.08354.
--
-- Every q_n is a genuine rational from K04a, with a signed integer
-- numerator and a strictly positive rational denominator. Factorise
-- each magnitude with the proof-bearing all-prime algorithm.  The
-- *complete* signed factors go to the residual tail; a subsequent
-- SSP15 dictionary split may compress them only with proof of exactly
-- equivalent reconstruction. Fixed SSP15 alone is NOT universal.
--
-- q_0=0 requires an explicit zero case (zero has no prime factors).
-- This is a total algorithm, NOT a guessed all-primes SSP representation.
-- Source-written; exact-head kernel receipt pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Z
import Data.Rational.Unnormalised as Q
import Data.Nat.ListAction as Product
import Data.Nat.Primality.Factorisation as Fact
import Data.List.Base as List
import Data.List.Relation.Unary.All as All
import Data.Nat.Primality as Prime
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Machin
import DASHI.Moonshine.AristotleHeckeGeneralPrimePowerDecompositionExact as Hecke
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP

-- Proof-bearing zero/nonzero classifier; no prime factors assigned to 0.
data FactorisationOrZero : Nat → Set where
  zeroFactorisation : FactorisationOrZero zero
  positiveFactorisation :
    {n : Nat} →
    Fact.PrimeFactorisation (suc n) →
    FactorisationOrZero (suc n)

factoriseOrZero : (n : Nat) → FactorisationOrZero n
factoriseOrZero zero = zeroFactorisation
factoriseOrZero (suc n) =
  positiveFactorisation
    (Hecke.canonicalRawPrimeFactorisation (suc n))

factorList : ∀ {n} → FactorisationOrZero n → List Nat
factorList zeroFactorisation = []
factorList (positiveFactorisation f) = Fact.factors f

factorListAllPrime :
  ∀ {n} (f : FactorisationOrZero n) →
  All.All Prime.Prime (factorList f)
factorListAllPrime zeroFactorisation = All.[]
factorListAllPrime (positiveFactorisation f) = Fact.factorsPrime f

factorProduct : List Nat → Nat
factorProduct = Product.product

decodeFactorisation : ∀ {n} → FactorisationOrZero n → Nat
decodeFactorisation zeroFactorisation = zero
decodeFactorisation (positiveFactorisation f) =
  factorProduct (Fact.factors f)

decodeFactorisationCorrect :
  ∀ {n} (f : FactorisationOrZero n) →
  decodeFactorisation f ≡ n
decodeFactorisationCorrect zeroFactorisation = refl
decodeFactorisationCorrect (positiveFactorisation f) =
  sym (Fact.isFactorisation f)

stage : Nat → Q.ℚᵘ
stage = Machin.qMachinStage

stageSignedNumerator : Nat → Z.ℤ
stageSignedNumerator n = Q.↥ (stage n)

stageNumeratorMagnitude : Nat → Nat
stageNumeratorMagnitude n = Z.∣ stageSignedNumerator n ∣

stageDenominator : Nat → Nat
stageDenominator n = Q.↧ₙ (stage n)

numeratorFactorisation : (n : Nat) →
  FactorisationOrZero (stageNumeratorMagnitude n)
numeratorFactorisation n = factoriseOrZero (stageNumeratorMagnitude n)

denominatorFactorisation : (n : Nat) →
  FactorisationOrZero (stageDenominator n)
denominatorFactorisation n = factoriseOrZero (stageDenominator n)

numeratorReconstructs : (n : Nat) →
  decodeFactorisation (numeratorFactorisation n)
    ≡ stageNumeratorMagnitude n
numeratorReconstructs n =
  decodeFactorisationCorrect (numeratorFactorisation n)

denominatorReconstructs : (n : Nat) →
  decodeFactorisation (denominatorFactorisation n)
    ≡ stageDenominator n
denominatorReconstructs n =
  decodeFactorisationCorrect (denominatorFactorisation n)

-- An exact lossless fallback into the existing compression interface:
-- the entire certified prime list is retained rather than silently
-- discarding primes outside the tracked SSP15.  Multiplicity is encoded
-- by repetition, not by pretending all exponents are 1 in the source.
positivePrimeCode : Nat → Compression.PrimeExponent
positivePrimeCode p =
  Compression.primeExponent p (SSP.positiveMultiplicity 1)

negativePrimeCode : Nat → Compression.PrimeExponent
negativePrimeCode p =
  Compression.primeExponent p (SSP.negativeMultiplicity 1)

stageResidualCompression : Nat → Compression.PrimeCompressionFibre
stageResidualCompression n =
  Compression.prime-compression-fibre
    []
    ( List.map positivePrimeCode
        (factorList (numeratorFactorisation n))
      List.++ List.map negativePrimeCode
        (factorList (denominatorFactorisation n)) )

-- The ORIGINAL signed numerator is retained separately from its
-- absolute-value factorization. This prevents losing the q_n sign.
record CertifiedRationalStage (n : Nat) : Set where
  constructor certified-rational-stage
  field
    signedNumerator : Z.ℤ
    denominator : Nat
    sourceEquals : signedNumerator ≡ stageSignedNumerator n
    denominatorEquals : denominator ≡ stageDenominator n
    numeratorDecodes :
      decodeFactorisation (numeratorFactorisation n)
        ≡ stageNumeratorMagnitude n
    denominatorDecodes :
      decodeFactorisation (denominatorFactorisation n)
        ≡ stageDenominator n
    allNumeratorFactorsPrime :
      All.All Prime.Prime (factorList (numeratorFactorisation n))
    allDenominatorFactorsPrime :
      All.All Prime.Prime (factorList (denominatorFactorisation n))
    residualCodec : Compression.PrimeCompressionFibre
    residualCodecIsComplete :
      residualCodec ≡ stageResidualCompression n

canonicalStage : (n : Nat) → CertifiedRationalStage n
canonicalStage n =
  certified-rational-stage
    (stageSignedNumerator n)
    (stageDenominator n)
    refl refl
    (numeratorReconstructs n)
    (denominatorReconstructs n)
    (factorListAllPrime (numeratorFactorisation n))
    (factorListAllPrime (denominatorFactorisation n))
    (stageResidualCompression n)
    refl

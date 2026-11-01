module DASHI.Analysis.BishopMachinSSP15PrimeDictionarySplitExact where

------------------------------------------------------------------------
-- K04c: CANONICAL SSP15 DICTIONARY / RESIDUAL SPLIT OF CERTIFIED
-- ALL-PRIME FACTORISATIONS, WITH EXACT MULTIPLICATIVE RECONSTRUCTION.
--
-- Reuse:
--  * original SignedSSPFRACTRANWeaveExact.canonicalSSPPrimes,
--    not a newly invented fifteen-prime vocabulary;
--  * original AristotleHeckeGeneralPrimePowerDecompositionExact's
--    Agda standard-library factorise owner;
--  * K04a actual rational q_n and its signed numerator/denominator;
--  * original QuadraticApproximationPrimeCompressionBidiExact codec.
-- Original source of prime factorisation: Euclid/fundamental theorem
-- of arithmetic and Agda stdlib Data.Nat.Primality.Factorisation.
--
-- Real *prime certificates*, exact product preservation and negative
-- denominator orientation survive the split. This is finite arithmetic:
-- there is no claim of a complete SSP-only encoding, analytic zeta,
-- optimal compression, Monster representation or primality shortcut.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Nat.Properties as NatP
import Data.Nat.ListAction as Product
import Data.List.Base as List
import Data.List.Relation.Unary.All as All
import Data.Nat.Primality as Prime
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Analysis.BishopMachinPrimeFactorStageExact as Raw
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Codec

natEqualBool : Nat → Nat → Bool
natEqualBool a b with NatP._≟_ a b
... | yes eq = true
... | no neq = false

isSSP15Prime : Nat → Bool
isSSP15Prime p =
  List.any
    (λ lane → natEqualBool p (SSP.primeValue lane))
    SSP.canonicalSSPPrimes

-- Complete typed proof-carrying split for any list of CERTIFIED primes.
-- All powers are represented by repetitions, not incorrectly discarded.
record CertifiedSplit (xs : List Nat) : Set where
  constructor certified-split
  field
    dictionary residual : List Nat
    productAgreement :
      Product.product xs ≡
        Product.product dictionary * Product.product residual
    dictionaryAreSSP :
      All.All (λ p → isSSP15Prime p ≡ true) dictionary
    residualAreNonSSP :
      All.All (λ p → isSSP15Prime p ≡ false) residual
    dictionaryFactorsPrime : All.All Prime.Prime dictionary
    residualFactorsPrime : All.All Prime.Prime residual
open CertifiedSplit public

splitCertified :
  (xs : List Nat) →
  All.All Prime.Prime xs →
  CertifiedSplit xs
splitCertified [] proofs =
  certified-split [] [] refl All.[] All.[] All.[] All.[]
splitCertified (p ∷ ps) proofs
  with isSSP15Prime p | splitCertified ps (All.tail proofs)
... | true | rest =
  certified-split
    (p ∷ dictionary rest)
    (residual rest)
    (trans
      (cong (p *_) (productAgreement rest))
      (sym (NatP.*-assoc p
        (Product.product (dictionary rest))
        (Product.product (residual rest)))))
    (All._∷_ refl (dictionaryAreSSP rest))
    (residualAreNonSSP rest)
    (All._∷_ (All.head proofs) (dictionaryFactorsPrime rest))
    (residualFactorsPrime rest)
... | false | rest =
  certified-split
    (dictionary rest)
    (p ∷ residual rest)
    (trans
      (cong (p *_) (productAgreement rest))
      (trans
        (sym (NatP.*-assoc p
          (Product.product (dictionary rest))
          (Product.product (residual rest))))
        (trans
          (cong
            (λ x → x * Product.product (residual rest))
            (NatP.*-comm p (Product.product (dictionary rest))))
          (NatP.*-assoc
            (Product.product (dictionary rest))
            p
            (Product.product (residual rest))))))
    (dictionaryAreSSP rest)
    (All._∷_ refl (residualAreNonSSP rest))
    (dictionaryFactorsPrime rest)
    (All._∷_ (All.head proofs) (residualFactorsPrime rest))

numeratorSplit : (n : Nat) →
  CertifiedSplit
    (Raw.factorList (Raw.numeratorFactorisation n))
numeratorSplit n =
  splitCertified
    (Raw.factorList (Raw.numeratorFactorisation n))
    (Raw.factorListAllPrime (Raw.numeratorFactorisation n))

denominatorSplit : (n : Nat) →
  CertifiedSplit
    (Raw.factorList (Raw.denominatorFactorisation n))
denominatorSplit n =
  splitCertified
    (Raw.factorList (Raw.denominatorFactorisation n))
    (Raw.factorListAllPrime (Raw.denominatorFactorisation n))

-- Existing codec: numerator factors have positive, denominator factors
-- negative FRACTRAN exponent. Signed NUMERATOR integer remains retained
-- separately by Raw.canonicalStage, including zero or negative cases.
stageSSP15Codec : Nat → Codec.PrimeCompressionFibre
stageSSP15Codec n =
  Codec.prime-compression-fibre
    (List._++_
      (List.map Raw.positivePrimeCode (dictionary (numeratorSplit n)))
      (List.map Raw.negativePrimeCode (dictionary (denominatorSplit n))))
    (List._++_
      (List.map Raw.positivePrimeCode (residual (numeratorSplit n)))
      (List.map Raw.negativePrimeCode (residual (denominatorSplit n))))

-- Decode equality to original signed rational stage's raw magnitudes.
-- The equality is exact on the ACTUAL two finite factor lists and
-- doesn't infer any analytic prime estimate.
numeratorProductBidi : ∀ n →
  Product.product (Raw.factorList (Raw.numeratorFactorisation n))
    ≡ Product.product (dictionary (numeratorSplit n)) *
      Product.product (residual (numeratorSplit n))
numeratorProductBidi n = productAgreement (numeratorSplit n)

denominatorProductBidi : ∀ n →
  Product.product (Raw.factorList (Raw.denominatorFactorisation n))
    ≡ Product.product (dictionary (denominatorSplit n)) *
      Product.product (residual (denominatorSplit n))
denominatorProductBidi n = productAgreement (denominatorSplit n)

-- The source rational stage is still present and algebraically
-- reconstructed by Raw.numeratorReconstructs/denominatorReconstructs.
-- A zero numerator is handled by Raw.zeroFactorisation and never
-- reinterpreted as an empty factor product (=1).

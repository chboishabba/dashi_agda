module DASHI.Crypto.FiniteFactorArithmetic where

open import DASHI.Core.Prelude
open import DASHI.Foundations.Base369Nat using (NonZero; nonZero)
open import DASHI.Crypto.RSAArithmeticCore using (powMod)

------------------------------------------------------------------------
-- Finite arithmetic certificates used by Shor factor extraction.
------------------------------------------------------------------------

Positive : Nat → Set
Positive n = Σ Nat (λ k → n ≡ suc k)

AtLeastTwo : Nat → Set
AtLeastTwo n = Σ Nat (λ k → n ≡ suc (suc k))

record FactorCertificate (N d : Nat) : Set where
  constructor mkFactorCertificate
  field
    cofactor : Nat
    factorAtLeastTwo : AtLeastTwo d
    cofactorAtLeastTwo : AtLeastTwo cofactor
    factorization : d * cofactor ≡ N

open FactorCertificate public

record CommonFactorCertificate (N u : Nat) : Set where
  constructor mkCommonFactorCertificate
  field
    commonFactor : Nat
    modulusFactor : FactorCertificate N commonFactor
    auxiliaryCofactor : Nat
    auxiliaryFactorization : commonFactor * auxiliaryCofactor ≡ u

open CommonFactorCertificate public

forgetAuxiliaryFactor :
  ∀ {N u} →
  CommonFactorCertificate N u →
  Σ Nat (λ d → FactorCertificate N d)
forgetAuxiliaryFactor C = commonFactor C , modulusFactor C

record EvenCertificate (n : Nat) : Set where
  constructor mkEvenCertificate
  field
    half : Nat
    evenLaw : n ≡ half + half

open EvenCertificate public

record PeriodCertificate (N a r : Nat) : Set where
  constructor mkPeriodCertificate
  field
    modulusNonZero : NonZero N
    positivePeriod : Positive r
    periodLaw : powMod a r N {{modulusNonZero}} ≡ 1

open PeriodCertificate public

record ExactOrderCertificate (N a r : Nat) : Set where
  constructor mkExactOrderCertificate
  field
    periodCertificate : PeriodCertificate N a r
    earlierNonperiod :
      ∀ k →
      Positive k →
      k < r →
      ¬ (powMod a k N {{modulusNonZero periodCertificate}} ≡ 1)

open ExactOrderCertificate public

record CertifiedShorSplit (N a r : Nat) : Set where
  constructor mkCertifiedShorSplit
  field
    splitPeriod : PeriodCertificate N a r
    splitEven : EvenCertificate r
    halfPower : Nat
    halfPowerLaw :
      halfPower ≡
      powMod a (half splitEven) N {{modulusNonZero splitPeriod}}
    splitBranch :
      CommonFactorCertificate N (halfPower ∸ 1) ⊎
      CommonFactorCertificate N (halfPower + 1)

open CertifiedShorSplit public

extractCertifiedFactor :
  ∀ {N a r} →
  CertifiedShorSplit N a r →
  Σ Nat (λ d → FactorCertificate N d)
extractCertifiedFactor S with splitBranch S
... | inj₁ C = forgetAuxiliaryFactor C
... | inj₂ C = forgetAuxiliaryFactor C

factor3Of15 : FactorCertificate 15 3
factor3Of15 = record
  { cofactor = 5
  ; factorAtLeastTwo = 1 , refl
  ; cofactorAtLeastTwo = 3 , refl
  ; factorization = refl
  }

common3Of3Modulo15 : CommonFactorCertificate 15 3
common3Of3Modulo15 = record
  { commonFactor = 3
  ; modulusFactor = factor3Of15
  ; auxiliaryCofactor = 1
  ; auxiliaryFactorization = refl
  }

period2Mod15Four : PeriodCertificate 15 2 4
period2Mod15Four = record
  { modulusNonZero = nonZero
  ; positivePeriod = 3 , refl
  ; periodLaw = refl
  }

evenFour : EvenCertificate 4
evenFour = record
  { half = 2
  ; evenLaw = refl
  }

shorSplit15 : CertifiedShorSplit 15 2 4
shorSplit15 = record
  { splitPeriod = period2Mod15Four
  ; splitEven = evenFour
  ; halfPower = 4
  ; halfPowerLaw = refl
  ; splitBranch = inj₁ common3Of3Modulo15
  }

factor7Of21 : FactorCertificate 21 7
factor7Of21 = record
  { cofactor = 3
  ; factorAtLeastTwo = 5 , refl
  ; cofactorAtLeastTwo = 1 , refl
  ; factorization = refl
  }

common7Of7Modulo21 : CommonFactorCertificate 21 7
common7Of7Modulo21 = record
  { commonFactor = 7
  ; modulusFactor = factor7Of21
  ; auxiliaryCofactor = 1
  ; auxiliaryFactorization = refl
  }

period2Mod21Six : PeriodCertificate 21 2 6
period2Mod21Six = record
  { modulusNonZero = nonZero
  ; positivePeriod = 5 , refl
  ; periodLaw = refl
  }

evenSix : EvenCertificate 6
evenSix = record
  { half = 3
  ; evenLaw = refl
  }

shorSplit21 : CertifiedShorSplit 21 2 6
shorSplit21 = record
  { splitPeriod = period2Mod21Six
  ; splitEven = evenSix
  ; halfPower = 8
  ; halfPowerLaw = refl
  ; splitBranch = inj₁ common7Of7Modulo21
  }

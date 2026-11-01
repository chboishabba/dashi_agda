module DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact where

------------------------------------------------------------------------
-- PUBLISHED DELIGNE--DWORK COEFFICIENT FAMILY ON THE ACTUAL LOCAL CARRIER
--
-- PRIMARY SOURCES
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
-- In particular Section 7 and Theorem 8.2.
--
-- Masao Koike,
-- "Congruences between modular forms and functions and applications to the
-- conjecture of Atkin", J. Fac. Sci. Univ. Tokyo Sect. IA Math. 20 (1973),
-- 129--169. Repository identifier: 10.15083/00039793.
--
-- Holly Swisher,
-- "A remark on Hecke operators and a theorem of Dwork and Koike",
-- Illinois J. Math. 48 (2004), 353--356.
-- DOI: 10.1215/ijm/1258136188.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 states, for prime p, that there are integer coefficients
-- A_n(alpha^) with
--
--   p J_1|U_p
--     = - sum_alpha sum_{n>=1}
--         A_n(alpha^) (J_1-alpha^)^{-n}.
--
-- DASHI CONTRIBUTION
--
-- Construct the previously type-only Dwork pole family from ONE published
-- prime-indexed integer family and embed every A_n(alpha^) into the SAME local
-- carrier used by the exceptional Hensel/Legendre lift.  A_1 is definitionally
-- the n=1 member; it is never stored as a second independent coefficient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact as Pole
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel

postulate
  DeligneDworkKoikePartialFractionExpansion :
    Nat → ℤ → (Pole.PositivePoleOrder → ℤ) → Set

record PublishedDworkCoefficientSource
    {branch : Legendre.ExceptionalLegendreBranch}
    (S : Hensel.ExceptionalHenselLocalSource branch) : Set₁ where
  field
    prime : Nat
    primeIsPrime : Prime prime
    alphaHat : ℤ
    integerCoefficient : Pole.PositivePoleOrder → ℤ
    proposition31Expansion :
      DeligneDworkKoikePartialFractionExpansion
        prime alphaHat integerCoefficient
    embedInteger : ℤ → Hensel.PadicLocal S

open PublishedDworkCoefficientSource public

actualDworkPoleFamily :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {S : Hensel.ExceptionalHenselLocalSource branch} →
  PublishedDworkCoefficientSource S → Pole.DworkPoleCoefficientFamily
actualDworkPoleFamily {S = S} C = record
  { Pole.PadicLocal = Hensel.PadicLocal S
  ; Pole.poleCoefficient = λ n → embedInteger C (integerCoefficient C n)
  }

actualAn :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {S : Hensel.ExceptionalHenselLocalSource branch} →
  (C : PublishedDworkCoefficientSource S) →
  Pole.PositivePoleOrder → Hensel.PadicLocal S
actualAn C = Pole.poleCoefficient (actualDworkPoleFamily C)

actualA1 :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {S : Hensel.ExceptionalHenselLocalSource branch} →
  (C : PublishedDworkCoefficientSource S) → Hensel.PadicLocal S
actualA1 C = Pole.firstPoleCoefficient (actualDworkPoleFamily C)

actualA1IsEmbeddedPublishedOrderOne :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {S : Hensel.ExceptionalHenselLocalSource branch} →
  (C : PublishedDworkCoefficientSource S) →
  actualA1 C
  ≡ embedInteger C (integerCoefficient C Pole.firstPoleOrder)
actualA1IsEmbeddedPublishedOrderOne C = refl

actualA1IsFamilyCoefficientOne :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {S : Hensel.ExceptionalHenselLocalSource branch} →
  (C : PublishedDworkCoefficientSource S) →
  actualA1 C ≡ actualAn C (Pole.onePlus 0)
actualA1IsFamilyCoefficientOne C = refl

publishedExpansionUsesActualIntegerFamily :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {S : Hensel.ExceptionalHenselLocalSource branch} →
  (C : PublishedDworkCoefficientSource S) →
  DeligneDworkKoikePartialFractionExpansion
    (prime C) (alphaHat C) (integerCoefficient C)
publishedExpansionUsesActualIntegerFamily = proposition31Expansion

record DuncanSwisherDworkPublishedCoefficientFamilyBoundary : Set where
  field
    sourcePrimeProofRequired : Bool
    proposition31FamilyIsIntegerValued : Bool
    coefficientFamilyConstructedForEveryPositivePoleOrder : Bool
    samePadicCarrierAsLegendreLift : Bool
    A1StoredIndependently : Bool
    A1DefinitionallyOrderOne : Bool
    sourceExpansionTiedToSameIntegerFamily : Bool
    infiniteAnalyticExpansionReprovedHere : Bool
    firstPoleSharpnessProvedHere : Bool

canonicalDuncanSwisherDworkPublishedCoefficientFamilyBoundary :
  DuncanSwisherDworkPublishedCoefficientFamilyBoundary
canonicalDuncanSwisherDworkPublishedCoefficientFamilyBoundary = record
  { sourcePrimeProofRequired = true
  ; proposition31FamilyIsIntegerValued = true
  ; coefficientFamilyConstructedForEveryPositivePoleOrder = true
  ; samePadicCarrierAsLegendreLift = true
  ; A1StoredIndependently = false
  ; A1DefinitionallyOrderOne = true
  ; sourceExpansionTiedToSameIntegerFamily = true
  ; infiniteAnalyticExpansionReprovedHere = false
  ; firstPoleSharpnessProvedHere = false
  }

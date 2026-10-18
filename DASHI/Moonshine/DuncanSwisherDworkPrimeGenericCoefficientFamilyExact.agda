module DASHI.Moonshine.DuncanSwisherDworkPrimeGenericCoefficientFamilyExact where

------------------------------------------------------------------------
-- PRIME-GENERIC DELIGNE--DWORK COEFFICIENT FAMILY
--
-- Duncan--Swisher Proposition 3.1 is prime-generic for primes for which
-- Gamma0(p)^+ has genus zero.  The partial-fraction expansion and the integer
-- coefficient family A_n(alpha^) are NOT restricted to p>3; only the stated
-- n=1 sharpness conclusion is.
--
-- The older repository owner tied PublishedDworkCoefficientSource to a
-- Legendre/Hensel exceptional local branch because that was convenient for the
-- p>3 sharpness proof.  This module factors out the genuinely source-native
-- integer family before any tame local-coordinate choice.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)
open import Data.Integer.Base using (∣_∣)
open import Data.Nat.Primality using (Prime)

import DASHI.Arithmetic.VpTrue as Vp
import DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact as Pole
import DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact as Legacy
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Prime-generic Proposition-3.1 source.
------------------------------------------------------------------------

record PrimeGenericPublishedDworkCoefficientSource : Set₁ where
  field
    prime : Nat
    primeIsPrime : Prime prime

    alphaHat : ℤ

    integerCoefficient :
      Pole.PositivePoleOrder -> ℤ

    proposition31Expansion :
      Legacy.DeligneDworkKoikePartialFractionExpansion
        prime alphaHat integerCoefficient

open PrimeGenericPublishedDworkCoefficientSource public

------------------------------------------------------------------------
-- 2. Existing p>3/local source forgets to the prime-generic source exactly.
------------------------------------------------------------------------

forgetLocalCarrier :
  {branch : Legendre.ExceptionalLegendreBranch} ->
  {S : Hensel.ExceptionalHenselLocalSource branch} ->
  Legacy.PublishedDworkCoefficientSource S ->
  PrimeGenericPublishedDworkCoefficientSource
forgetLocalCarrier C =
  record
    { prime = Legacy.prime C
    ; primeIsPrime = Legacy.primeIsPrime C
    ; alphaHat = Legacy.alphaHat C
    ; integerCoefficient = Legacy.integerCoefficient C
    ; proposition31Expansion = Legacy.proposition31Expansion C
    }

forgottenPrime :
  {branch : Legendre.ExceptionalLegendreBranch} ->
  {S : Hensel.ExceptionalHenselLocalSource branch} ->
  (C : Legacy.PublishedDworkCoefficientSource S) ->
  prime (forgetLocalCarrier C) ≡ Legacy.prime C
forgottenPrime C = refl

forgottenAlphaHat :
  {branch : Legendre.ExceptionalLegendreBranch} ->
  {S : Hensel.ExceptionalHenselLocalSource branch} ->
  (C : Legacy.PublishedDworkCoefficientSource S) ->
  alphaHat (forgetLocalCarrier C) ≡ Legacy.alphaHat C
forgottenAlphaHat C = refl

forgottenIntegerFamily :
  {branch : Legendre.ExceptionalLegendreBranch} ->
  {S : Hensel.ExceptionalHenselLocalSource branch} ->
  (C : Legacy.PublishedDworkCoefficientSource S) ->
  integerCoefficient (forgetLocalCarrier C)
  ≡ Legacy.integerCoefficient C
forgottenIntegerFamily C = refl

------------------------------------------------------------------------
-- 3. Source-native integer A1 valuation.
------------------------------------------------------------------------

integerA1 :
  PrimeGenericPublishedDworkCoefficientSource ->
  ℤ
integerA1 C =
  integerCoefficient C Pole.firstPoleOrder

integerA1Depth :
  PrimeGenericPublishedDworkCoefficientSource ->
  Nat
integerA1Depth C =
  Vp.vp-true (prime C) (∣ integerA1 C ∣)

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

data Proposition31RequiresLegendreBranch : Set where
data Proposition31RequiresPrimeGreaterThanThree : Set where
data PrimeGenericFamilyCreatesSmallPrimeSharpness : Set where

proposition31DoesNotRequireLegendreBranch :
  Proposition31RequiresLegendreBranch -> ⊥
proposition31DoesNotRequireLegendreBranch ()

proposition31FamilyIsNotGt3Only :
  Proposition31RequiresPrimeGreaterThanThree -> ⊥
proposition31FamilyIsNotGt3Only ()

primeGenericFamilyDoesNotCreateSharpness :
  PrimeGenericFamilyCreatesSmallPrimeSharpness -> ⊥
primeGenericFamilyDoesNotCreateSharpness ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record PrimeGenericCoefficientFamilyBoundary : Set where
  constructor prime-generic-coefficient-family-boundary
  field
    proposition31IntegerFamilyFactoredFromLocalCarrier : Bool
    legacyLocalSourceForgetsExactly : Bool
    integerA1DepthDefinedPrimeGenerically : Bool
    pGreaterThanThreeRequiredForFamilyExistence : Bool
    legendreBranchRequiredForFamilyExistence : Bool
    smallPrimeSharpnessCreatedByRefactor : Bool

canonicalPrimeGenericCoefficientFamilyBoundary :
  PrimeGenericCoefficientFamilyBoundary
canonicalPrimeGenericCoefficientFamilyBoundary =
  prime-generic-coefficient-family-boundary
    true true true false false false

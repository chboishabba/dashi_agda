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
-- Proposition 3.1 states that there are integer coefficients A_n(alpha^) with
--
--   p J_1|U_p
--     = - sum_alpha sum_{n>=1}
--         A_n(alpha^) (J_1-alpha^)^{-n}.
--
-- DASHI CONTRIBUTION
--
-- The previous `DworkPoleCoefficientFamily` was only a type.  This module
-- constructs that family from ONE source-native Proposition-3.1 integer family
-- and embeds every A_n(alpha^) into the SAME p-adic carrier already used by the
-- exceptional Hensel/Legendre lift.
--
-- Crucially, A_1 is still not stored independently: it remains definitionally
-- the n=1 member of this actual family.  Infinite analytic convergence is kept
-- at the named source relation below; no fake finite summation is introduced.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)

import DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact as Pole
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel

------------------------------------------------------------------------
-- Abstract NAME for the published analytic partial-fraction identity.  It is a
-- relation on the actual integer coefficient function, not a Boolean receipt.
-- A source adapter inhabiting this relation is asserting Proposition 3.1 itself.
------------------------------------------------------------------------

postulate
  DeligneDworkKoikePartialFractionExpansion :
    Nat → ℤ → (Pole.PositivePoleOrder → ℤ) → Set

------------------------------------------------------------------------
-- One published coefficient family at one lifted exceptional residue point.
------------------------------------------------------------------------

record PublishedDworkCoefficientSource
    {branch : Legendre.ExceptionalLegendreBranch}
    (S : Hensel.ExceptionalHenselLocalSource branch) : Set₁ where
  field
    prime : Nat
    alphaHat : ℤ

    -- The actual source integers A_n(alpha^), n>=1.
    integerCoefficient : Pole.PositivePoleOrder → ℤ

    proposition31Expansion :
      DeligneDworkKoikePartialFractionExpansion
        prime alphaHat integerCoefficient

    -- Canonical embedding of source integers into this SAME local carrier.
    embedInteger : ℤ → Hensel.PadicLocal S

open PublishedDworkCoefficientSource public

------------------------------------------------------------------------
-- Actual A_n(alpha^) on the p-adic Legendre carrier.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- The source expansion remains tied to the SAME integer family used above.
------------------------------------------------------------------------

publishedExpansionUsesActualIntegerFamily :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {S : Hensel.ExceptionalHenselLocalSource branch} →
  (C : PublishedDworkCoefficientSource S) →
  DeligneDworkKoikePartialFractionExpansion
    (prime C) (alphaHat C) (integerCoefficient C)
publishedExpansionUsesActualIntegerFamily = proposition31Expansion

record DuncanSwisherDworkPublishedCoefficientFamilyBoundary : Set where
  field
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
  { proposition31FamilyIsIntegerValued = true
  ; coefficientFamilyConstructedForEveryPositivePoleOrder = true
  ; samePadicCarrierAsLegendreLift = true
  ; A1StoredIndependently = false
  ; A1DefinitionallyOrderOne = true
  ; sourceExpansionTiedToSameIntegerFamily = true
  ; infiniteAnalyticExpansionReprovedHere = false
  ; firstPoleSharpnessProvedHere = false
  }

module DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact where

------------------------------------------------------------------------
-- SAME-OBJECT FIRST-POLE COEFFICIENT FOR THE DELIGNE/DWORK EXPANSION
--
-- PRIMARY SOURCES
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
--
-- Masao Koike,
-- "Congruences between modular forms and functions and applications to the
-- conjecture of Atkin", J. Fac. Sci. Univ. Tokyo Sect. IA Math. 20 (1973),
-- 129--169. Repository identifier/DOI: 10.15083/00039793.
--
-- Holly Swisher,
-- "A remark on Hecke operators and a theorem of Dwork and Koike",
-- Illinois J. Math. 48 (2004), 353--356. DOI: 10.1215/ijm/1258136188.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 writes the partial-fraction coefficients as A_n(alpha^).
--
-- DASHI CONTRIBUTION
--
-- Eliminate a same-object ambiguity in the local sharpness lane.  The source
-- object is a positive-pole-order family
--
--   n |-> A_n(alpha^), n >= 1.
--
-- `firstPoleCoefficient` is DEFINITIONALLY the order-one member.  A later
-- sharpness theorem therefore cannot silently introduce a second unrelated
-- element merely named `A1` and then attach the desired valuation to it.
--
-- This module does not construct the analytic coefficient family.  It fixes
-- the theorem interface that a genuine Deligne/Dwork source adapter must
-- inhabit.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Positive pole orders: onePlus n represents analytic order n+1.
------------------------------------------------------------------------

data PositivePoleOrder : Set where
  onePlus : Nat -> PositivePoleOrder

poleOrderValue : PositivePoleOrder -> Nat
poleOrderValue (onePlus n) = suc n

firstPoleOrder : PositivePoleOrder
firstPoleOrder = onePlus 0

firstPoleOrderIsOne : poleOrderValue firstPoleOrder ≡ 1
firstPoleOrderIsOne = refl

------------------------------------------------------------------------
-- One source-native coefficient family at one lifted supersingular point.
------------------------------------------------------------------------

record DworkPoleCoefficientFamily : Set₁ where
  field
    PadicLocal : Set
    poleCoefficient : PositivePoleOrder -> PadicLocal

open DworkPoleCoefficientFamily public

firstPoleCoefficient :
  (F : DworkPoleCoefficientFamily) -> PadicLocal F
firstPoleCoefficient F = poleCoefficient F firstPoleOrder

firstPoleIsFamilyOrderOne :
  (F : DworkPoleCoefficientFamily) ->
  firstPoleCoefficient F ≡ poleCoefficient F (onePlus 0)
firstPoleIsFamilyOrderOne F = refl

------------------------------------------------------------------------
-- Optional full partial-fraction source surface.  The family is shared; A1 is
-- not stored again.
------------------------------------------------------------------------

record DworkPartialFractionFamilySource : Set₁ where
  field
    coefficients : DworkPoleCoefficientFamily

    JDifference : Set

    -- A source adapter may retain the actual pole denominator/power object
    -- separately from the coefficient carrier.  We do not fabricate infinite
    -- summation or analytic convergence here.
    poleDenominator : JDifference
    polePower : PositivePoleOrder -> JDifference

open DworkPartialFractionFamilySource public

sourceFirstPoleCoefficient :
  (S : DworkPartialFractionFamilySource) ->
  PadicLocal (coefficients S)
sourceFirstPoleCoefficient S = firstPoleCoefficient (coefficients S)

record DuncanSwisherDworkFirstPoleSameObjectBoundary : Set where
  field
    positivePoleOrderTyped : Bool
    coefficientFamilyPrimary : Bool
    A1StoredAsSecondIndependentElement : Bool
    firstPoleDefinitionallyOrderOne : Bool
    fullAnalyticFamilyConstructedHere : Bool
    infinitePartialFractionConvergenceConstructedHere : Bool
    firstPoleSharpnessProvedHere : Bool

canonicalDuncanSwisherDworkFirstPoleSameObjectBoundary :
  DuncanSwisherDworkFirstPoleSameObjectBoundary
canonicalDuncanSwisherDworkFirstPoleSameObjectBoundary = record
  { positivePoleOrderTyped = true
  ; coefficientFamilyPrimary = true
  ; A1StoredAsSecondIndependentElement = false
  ; firstPoleDefinitionallyOrderOne = true
  ; fullAnalyticFamilyConstructedHere = false
  ; infinitePartialFractionConvergenceConstructedHere = false
  ; firstPoleSharpnessProvedHere = false
  }

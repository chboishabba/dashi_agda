module DASHI.Moonshine.DuncanSwisherDworkPublishedFirstPoleSharpnessExact where

------------------------------------------------------------------------
-- PUBLISHED DWORK n=1 SHARPNESS -> SAME-OBJECT LEGENDRE DEPTH EQUALITY
--
-- PRIMARY SOURCES
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
-- Theorem 8.2 gives the ordinary n=1 sharp value; the beginning of Section
-- 7.e gives the exceptional Legendre-coordinate modifications.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1, equations (3.1)--(3.2), and its proof state that for p>3
-- the n=1 bounds are sharp: depth 3 at j=0, depth 2 at j=1728, depth 1 at
-- ordinary supersingular residues.
--
-- DASHI CONTRIBUTION
--
-- The previous analytic cutset imported the DESIRED equality
--
--     v_p(A_1(alpha^)) = v_p(J-alpha)
--
-- as one field.  Here the deep imported theorem is instead Dwork's actual
-- sharp n=1 statement on the SAME Proposition-3.1 family.  The Hensel/Legendre
-- side independently derives v_p(J-alpha)=the ramification exponent.  The
-- target equality is then a theorem by transitivity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel
import DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact as Lift
import DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact as Coeff
import DASHI.Moonshine.DuncanSwisherDworkExceptionalAnalyticCutsetExact as Analytic
import DASHI.Moonshine.DuncanSwisherDworkLiftedFirstPoleSharpnessExact as Lifted

------------------------------------------------------------------------
-- GENUINELY DEEP SOURCE THEOREM: Dwork Theorem 8.2 + Section 7.e exceptional
-- modification, as restated in the proof of Duncan--Swisher Proposition 3.1.
-- It is deliberately NOT phrased as a comparison with local J.
------------------------------------------------------------------------

postulate
  publishedDworkExceptionalFirstPoleSharpness :
    {branch : Legendre.ExceptionalLegendreBranch} →
    {S : Hensel.ExceptionalHenselLocalSource branch} →
    (C : Coeff.PublishedDworkCoefficientSource S) →
    4 ≤ Coeff.prime C →
    Ramified.valuation (Hensel.valuation S) (Coeff.actualA1 C)
    ≡ Legendre.exceptionalRamificationExponent branch

publishedJZeroA1DepthThree :
  {S : Hensel.ExceptionalHenselLocalSource Legendre.jZeroQuadraticBranch} →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  4 ≤ Coeff.prime C →
  Ramified.valuation (Hensel.valuation S) (Coeff.actualA1 C) ≡ 3
publishedJZeroA1DepthThree C gt3 =
  publishedDworkExceptionalFirstPoleSharpness C gt3

publishedJ1728MinusTwoA1DepthTwo :
  {S : Hensel.ExceptionalHenselLocalSource Legendre.j1728LambdaMinusTwo} →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  4 ≤ Coeff.prime C →
  Ramified.valuation (Hensel.valuation S) (Coeff.actualA1 C) ≡ 2
publishedJ1728MinusTwoA1DepthTwo C gt3 =
  publishedDworkExceptionalFirstPoleSharpness C gt3

------------------------------------------------------------------------
-- TARGET equality DERIVED from two independent source mechanisms.
------------------------------------------------------------------------

publishedA1TracksConstructedLocalJDepth :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : Hensel.ExceptionalHenselLocalSource branch) →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  4 ≤ Coeff.prime C →
  Ramified.valuation (Hensel.valuation S) (Coeff.actualA1 C)
  ≡ Ramified.valuation (Hensel.valuation S)
      (Lift.localJDifference (Hensel.constructExceptionalPadicLift branch S))
publishedA1TracksConstructedLocalJDepth branch S C gt3 =
  trans
    (publishedDworkExceptionalFirstPoleSharpness C gt3)
    (sym (Hensel.constructedLocalJDepth branch S))

------------------------------------------------------------------------
-- Build the previous high-level authority from the lower source theorem.
------------------------------------------------------------------------

asLiftedDworkFirstPoleAuthority :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : Hensel.ExceptionalHenselLocalSource branch) →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  4 ≤ Coeff.prime C →
  Lifted.LiftedDworkFirstPoleAuthority branch
asLiftedDworkFirstPoleAuthority branch S C gt3 = record
  { Lifted.localLift = Hensel.constructExceptionalPadicLift branch S
  ; Lifted.coefficientFamily = Coeff.actualDworkPoleFamily C
  ; Lifted.coefficientCarrierIsLiftCarrier = refl
  ; Lifted.firstPoleTracksLocalJ =
      publishedA1TracksConstructedLocalJDepth branch S C gt3
  }

assembledFirstPoleDepthIsRamificationExponent :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : Hensel.ExceptionalHenselLocalSource branch) →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  (gt3 : 4 ≤ Coeff.prime C) →
  Ramified.valuation (Hensel.valuation S)
    (Analytic.A1Coefficient
      (Lifted.asA1Transfer branch
        (asLiftedDworkFirstPoleAuthority branch S C gt3)))
  ≡ Legendre.exceptionalRamificationExponent branch
assembledFirstPoleDepthIsRamificationExponent branch S C gt3 =
  Lifted.liftedFirstPoleDepthIsAlgebraicExponent branch
    (asLiftedDworkFirstPoleAuthority branch S C gt3)

record DuncanSwisherDworkPublishedFirstPoleSharpnessBoundary : Set where
  field
    deepDworkN1SharpnessImportedOnActualFamily : Bool
    desiredA1EqualsJDepthImported : Bool
    localJDepthIndependentlyDerivedFromHenselLegendre : Bool
    A1EqualsLocalJDepthDerived : Bool
    oldTracksLocalJReceiptEliminatedByAdapter : Bool
    exactExceptionalDepthDerived : Bool
    fullDworkPadicCyclesReprovedHere : Bool

canonicalDuncanSwisherDworkPublishedFirstPoleSharpnessBoundary :
  DuncanSwisherDworkPublishedFirstPoleSharpnessBoundary
canonicalDuncanSwisherDworkPublishedFirstPoleSharpnessBoundary = record
  { deepDworkN1SharpnessImportedOnActualFamily = true
  ; desiredA1EqualsJDepthImported = false
  ; localJDepthIndependentlyDerivedFromHenselLegendre = true
  ; A1EqualsLocalJDepthDerived = true
  ; oldTracksLocalJReceiptEliminatedByAdapter = true
  ; exactExceptionalDepthDerived = true
  ; fullDworkPadicCyclesReprovedHere = false
  }

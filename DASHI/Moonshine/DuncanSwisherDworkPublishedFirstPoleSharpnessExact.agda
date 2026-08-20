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
-- 7.e explains the exceptional Legendre-coordinate modifications.  The
-- exceptional local behaviours are cubic at j=0 and quadratic at j=1728.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1, equations (3.1)--(3.2), and its proof explicitly state:
-- for p>3 the n=1 bounds are sharp; v_p(A_1)=3 at the residue corresponding
-- to j=0, v_p(A_1)=2 at the residue corresponding to j=1728, and 1 otherwise.
--
-- DASHI CONTRIBUTION
--
-- The old analytic cutset imported the DESIRED equality
--
--     v_p(A_1(alpha^)) = v_p(J-alpha)
--
-- as `tracksLocalJDepth`.
--
-- This file removes that receipt.  The deep imported Dwork theorem is instead
-- its actual source statement on the SAME Proposition-3.1 coefficient family:
-- the first-pole valuation equals the exceptional sharp depth 3 or 2.
-- Independently, the Hensel/Legendre construction proves
--
--     v_p(J-alpha) = exceptionalRamificationExponent.
--
-- The equality of the two valuations is then derived by transitivity.  Thus
-- the third requested hard theorem is present without postulating the target
-- comparison itself.
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
-- The genuinely deep source theorem.  It is NOT a comparison with J-alpha.
-- It states the n=1 sharp valuation on the actual Proposition-3.1 family.
------------------------------------------------------------------------

postulate
  publishedDworkExceptionalFirstPoleSharpness :
    {branch : Legendre.ExceptionalLegendreBranch} →
    {S : Hensel.ExceptionalHenselLocalSource branch} →
    (C : Coeff.PublishedDworkCoefficientSource S) →
    4 ≤ Coeff.prime C →
    Ramified.valuation (Hensel.valuation S) (Coeff.actualA1 C)
    ≡ Legendre.exceptionalRamificationExponent branch

------------------------------------------------------------------------
-- Source statement specialized to the two exceptional ramification types.
------------------------------------------------------------------------

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
-- The TARGET equality is now a theorem consequence, not source authority.
------------------------------------------------------------------------

publishedA1TracksConstructedLocalJDepth :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : Hensel.ExceptionalHenselLocalSource branch) →
  (nearby : Hensel.HenselNearbyResidueCompatibility S) →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  4 ≤ Coeff.prime C →
  Ramified.valuation (Hensel.valuation S) (Coeff.actualA1 C)
  ≡ Ramified.valuation (Hensel.valuation S)
      (Lift.localJDifference
        (Hensel.constructExceptionalPadicLift branch S nearby))
publishedA1TracksConstructedLocalJDepth branch S nearby C gt3 =
  trans
    (publishedDworkExceptionalFirstPoleSharpness C gt3)
    (sym (Hensel.constructedLocalJDepth branch S nearby))

------------------------------------------------------------------------
-- Build the OLD lifted-sharpness authority from the new, lower source surface.
-- This closes the former `tracksLocalJDepth` seam without assuming it.
------------------------------------------------------------------------

asLiftedDworkFirstPoleAuthority :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : Hensel.ExceptionalHenselLocalSource branch) →
  (nearby : Hensel.HenselNearbyResidueCompatibility S) →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  4 ≤ Coeff.prime C →
  Lifted.LiftedDworkFirstPoleAuthority branch
asLiftedDworkFirstPoleAuthority branch S nearby C gt3 = record
  { Lifted.localLift = Hensel.constructExceptionalPadicLift branch S nearby
  ; Lifted.coefficientFamily = Coeff.actualDworkPoleFamily C
  ; Lifted.coefficientCarrierIsLiftCarrier = refl
  ; Lifted.firstPoleTracksLocalJ =
      publishedA1TracksConstructedLocalJDepth branch S nearby C gt3
  }

------------------------------------------------------------------------
-- Existing downstream depth theorem now consumes a fully assembled object.
------------------------------------------------------------------------

assembledFirstPoleDepthIsRamificationExponent :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : Hensel.ExceptionalHenselLocalSource branch) →
  (nearby : Hensel.HenselNearbyResidueCompatibility S) →
  (C : Coeff.PublishedDworkCoefficientSource S) →
  (gt3 : 4 ≤ Coeff.prime C) →
  Ramified.valuation (Hensel.valuation S)
    (Analytic.A1Coefficient
      (Lifted.asA1Transfer branch
        (asLiftedDworkFirstPoleAuthority branch S nearby C gt3)))
  ≡ Legendre.exceptionalRamificationExponent branch
assembledFirstPoleDepthIsRamificationExponent branch S nearby C gt3 =
  Lifted.liftedFirstPoleDepthIsAlgebraicExponent branch
    (asLiftedDworkFirstPoleAuthority branch S nearby C gt3)

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

module DASHI.Moonshine.DuncanSwisherDworkExceptionalAnalyticCutsetExact where

------------------------------------------------------------------------
-- EXCEPTIONAL DWORK ANALYTIC CUTSET
--
-- PRIMARY SOURCES
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 uses the Deligne/Dwork/Koike partial-fraction expansion and
-- records that the n=1 valuation bounds are sharp for p>3.
--
-- DASHI CONTRIBUTION
--
-- Separate the two genuinely analytic authorities which remained conflated in
-- `DworkLocalSharpnessData`:
--
--   (A) local Legendre/J geometry on an ACTUAL exceptional branch;
--   (B) Dwork's first-pole transfer
--         v_p(A_{order 1}(alpha^)) = v_p(local J difference).
--
-- The A1 object is no longer stored independently: it is DEFINITIONALLY the
-- order-one member of one source-native partial-fraction coefficient family.
-- The exceptional exponent is likewise NOT supplied by either authority; it
-- is read from the exact Legendre polynomial factorization.
--
-- Consequently the exact first-pole depth is derived as
--
--   algebraic branch exponent
--     <- local J valuation theorem
--     <- Dwork order-one coefficient valuation transfer.
--
-- This module does not reconstruct Dwork's p-adic cycles or the analytic
-- coefficient family itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreJExceptionalLocalValuationCutsetExact as Local
import DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact as Pole

------------------------------------------------------------------------
-- Authority (A): actual local p-adic Legendre/J geometry.
------------------------------------------------------------------------

record ExceptionalLegendreGeometryAuthority
    (branch : Legendre.ExceptionalLegendreBranch) : Set₁ where
  field
    PadicLocal : Set
    valuation : Ramified.MultiplicativeNatValuation PadicLocal
    geometry : Local.ExceptionalLegendreLocalSharpness valuation branch

open ExceptionalLegendreGeometryAuthority public

------------------------------------------------------------------------
-- Authority (B): one source-native Dwork pole family on the SAME carrier, plus
-- the n=1 sharp valuation transfer.  There is no separately supplied A1 value.
------------------------------------------------------------------------

record DworkA1ValuationTransfer
    {branch : Legendre.ExceptionalLegendreBranch}
    (G : ExceptionalLegendreGeometryAuthority branch) : Set₁ where
  field
    coefficientFamily : Pole.DworkPoleCoefficientFamily
    coefficientCarrierIsLocal : Pole.PadicLocal coefficientFamily ≡ PadicLocal G

    tracksLocalJDepth :
      Ramified.valuation (valuation G)
        (subst (λ X → X) coefficientCarrierIsLocal
          (Pole.firstPoleCoefficient coefficientFamily))
      ≡ Ramified.valuation (valuation G)
          (Local.localJDifference (geometry G))

open DworkA1ValuationTransfer public

A1Coefficient :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {G : ExceptionalLegendreGeometryAuthority branch} →
  DworkA1ValuationTransfer G → PadicLocal G
A1Coefficient D =
  subst (λ X → X) (coefficientCarrierIsLocal D)
    (Pole.firstPoleCoefficient (coefficientFamily D))

A1IsSameObjectFirstPole :
  {branch : Legendre.ExceptionalLegendreBranch} →
  {G : ExceptionalLegendreGeometryAuthority branch} →
  (D : DworkA1ValuationTransfer G) →
  A1Coefficient D
  ≡ subst (λ X → X) (coefficientCarrierIsLocal D)
      (Pole.poleCoefficient (coefficientFamily D) Pole.firstPoleOrder)
A1IsSameObjectFirstPole D = refl

------------------------------------------------------------------------
-- Composition: exact A1 depth is theorem-derived.
------------------------------------------------------------------------

exceptionalA1DepthIsBranchExponent :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (G : ExceptionalLegendreGeometryAuthority branch) →
  (D : DworkA1ValuationTransfer G) →
  Ramified.valuation (valuation G) (A1Coefficient D)
  ≡ Legendre.exceptionalRamificationExponent branch
exceptionalA1DepthIsBranchExponent branch G D =
  trans
    (tracksLocalJDepth D)
    (Local.exceptionalLocalJDepthIsAlgebraicRamification
      (valuation G) branch (geometry G))

jZeroA1DepthThree :
  (G : ExceptionalLegendreGeometryAuthority Legendre.jZeroQuadraticBranch) →
  (D : DworkA1ValuationTransfer G) →
  Ramified.valuation (valuation G) (A1Coefficient D) ≡ 3
jZeroA1DepthThree G D =
  exceptionalA1DepthIsBranchExponent Legendre.jZeroQuadraticBranch G D

j1728MinusTwoA1DepthTwo :
  (G : ExceptionalLegendreGeometryAuthority Legendre.j1728LambdaMinusTwo) →
  (D : DworkA1ValuationTransfer G) →
  Ramified.valuation (valuation G) (A1Coefficient D) ≡ 2
j1728MinusTwoA1DepthTwo G D =
  exceptionalA1DepthIsBranchExponent Legendre.j1728LambdaMinusTwo G D

j1728PlusOneA1DepthTwo :
  (G : ExceptionalLegendreGeometryAuthority Legendre.j1728LambdaPlusOne) →
  (D : DworkA1ValuationTransfer G) →
  Ramified.valuation (valuation G) (A1Coefficient D) ≡ 2
j1728PlusOneA1DepthTwo G D =
  exceptionalA1DepthIsBranchExponent Legendre.j1728LambdaPlusOne G D

j1728HalfA1DepthTwo :
  (G : ExceptionalLegendreGeometryAuthority Legendre.j1728TwoLambdaMinusOne) →
  (D : DworkA1ValuationTransfer G) →
  Ramified.valuation (valuation G) (A1Coefficient D) ≡ 2
j1728HalfA1DepthTwo G D =
  exceptionalA1DepthIsBranchExponent Legendre.j1728TwoLambdaMinusOne G D

record DuncanSwisherDworkExceptionalAnalyticCutsetBoundary : Set where
  field
    localGeometryAuthoritySeparated : Bool
    A1ValuationTransferAuthoritySeparated : Bool
    coefficientFamilyPrimary : Bool
    A1StoredAsIndependentElement : Bool
    firstPoleDefinitionallyOrderOne : Bool
    branchExponentSuppliedByAnalyticAuthority : Bool
    branchExponentDerivedFromPolynomialFactorization : Bool
    numericA1DepthSuppliedBySource : Bool
    exactA1DepthDerivedAfterComposition : Bool
    fullDworkCyclesReconstructedHere : Bool

canonicalDuncanSwisherDworkExceptionalAnalyticCutsetBoundary :
  DuncanSwisherDworkExceptionalAnalyticCutsetBoundary
canonicalDuncanSwisherDworkExceptionalAnalyticCutsetBoundary = record
  { localGeometryAuthoritySeparated = true
  ; A1ValuationTransferAuthoritySeparated = true
  ; coefficientFamilyPrimary = true
  ; A1StoredAsIndependentElement = false
  ; firstPoleDefinitionallyOrderOne = true
  ; branchExponentSuppliedByAnalyticAuthority = false
  ; branchExponentDerivedFromPolynomialFactorization = true
  ; numericA1DepthSuppliedBySource = false
  ; exactA1DepthDerivedAfterComposition = true
  ; fullDworkCyclesReconstructedHere = false
  }

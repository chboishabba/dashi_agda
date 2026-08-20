module DASHI.Moonshine.DuncanSwisherDworkLiftedFirstPoleSharpnessExact where

------------------------------------------------------------------------
-- CONVERGENCE SURFACE: SAME-OBJECT LOCAL LIFT + SAME-OBJECT FIRST POLE
--
-- PRIMARY SOURCES
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 / sharp n=1 first-pole bounds for p>3.
--
-- DASHI CONTRIBUTION
--
-- Put the two genuinely source-facing analytic objects on ONE theorem surface:
--
--   1. an actual exceptional p-adic Legendre lift whose residue data,
--      uniformizer displacement, simple branch and J-factorization are all
--      same-object;
--   2. one actual Dwork partial-fraction coefficient family on that SAME local
--      carrier, with the source sharpness theorem for its order-one member.
--
-- Everything else is downstream:
--
--   exact Legendre polynomial factorization
--     -> algebraic branch exponent e
--   residue nonzero
--     -> unit depth zero
--   one uniformizer displacement
--     -> coordinate depth one
--   simple-root factorization
--     -> branch depth one
--   local J factorization
--     -> v(J-alpha)=e
--   Dwork first-pole transfer
--     -> v(A_1)=e.
--
-- This file does NOT construct Q_p, the lift, Dwork's coefficient family or the
-- sharpness theorem.  It makes those remaining authorities irreducible and
-- prevents the numeric depth from entering independently.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreJExceptionalLocalValuationCutsetExact as Local
import DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact as Lift
import DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact as Pole
import DASHI.Moonshine.DuncanSwisherDworkExceptionalAnalyticCutsetExact as Analytic

------------------------------------------------------------------------
-- One complete but still source-facing analytic package.
------------------------------------------------------------------------

record LiftedDworkFirstPoleAuthority
    (branch : Legendre.ExceptionalLegendreBranch) : Set₁ where
  field
    localLift : Lift.ExceptionalPadicLift branch

    coefficientFamily : Pole.DworkPoleCoefficientFamily
    coefficientCarrierIsLiftCarrier :
      Pole.PadicLocal coefficientFamily ≡ Lift.PadicLocal localLift

    firstPoleTracksLocalJ :
      Ramified.valuation (Lift.valuation localLift)
        (subst (λ X → X) coefficientCarrierIsLiftCarrier
          (Pole.firstPoleCoefficient coefficientFamily))
      ≡ Ramified.valuation (Lift.valuation localLift)
          (Lift.localJDifference localLift)

open LiftedDworkFirstPoleAuthority public

------------------------------------------------------------------------
-- Adapt the same lift to the already-proved analytic cutset.
------------------------------------------------------------------------

asGeometryAuthority :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : LiftedDworkFirstPoleAuthority branch) →
  Analytic.ExceptionalLegendreGeometryAuthority branch
asGeometryAuthority branch A = record
  { Analytic.PadicLocal = Lift.PadicLocal (localLift A)
  ; Analytic.valuation = Lift.valuation (localLift A)
  ; Analytic.geometry =
      Lift.Preferred.asExceptionalLocalSharpness
        (Lift.valuation (localLift A)) branch
        (Lift.asPreferredLocalProducer branch (localLift A))
  }

asA1Transfer :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : LiftedDworkFirstPoleAuthority branch) →
  Analytic.DworkA1ValuationTransfer (asGeometryAuthority branch A)
asA1Transfer branch A = record
  { Analytic.coefficientFamily = coefficientFamily A
  ; Analytic.coefficientCarrierIsLocal = coefficientCarrierIsLiftCarrier A
  ; Analytic.tracksLocalJDepth = firstPoleTracksLocalJ A
  }

------------------------------------------------------------------------
-- Exact first-pole depth is now a pure theorem consequence.
------------------------------------------------------------------------

liftedFirstPoleDepthIsAlgebraicExponent :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : LiftedDworkFirstPoleAuthority branch) →
  Ramified.valuation
    (Lift.valuation (localLift A))
    (Analytic.A1Coefficient (asA1Transfer branch A))
  ≡ Legendre.exceptionalRamificationExponent branch
liftedFirstPoleDepthIsAlgebraicExponent branch A =
  Analytic.exceptionalA1DepthIsBranchExponent
    branch (asGeometryAuthority branch A) (asA1Transfer branch A)

liftedJZeroFirstPoleDepthThree :
  (A : LiftedDworkFirstPoleAuthority Legendre.jZeroQuadraticBranch) →
  Ramified.valuation
    (Lift.valuation (localLift A))
    (Analytic.A1Coefficient
      (asA1Transfer Legendre.jZeroQuadraticBranch A))
  ≡ 3
liftedJZeroFirstPoleDepthThree A =
  liftedFirstPoleDepthIsAlgebraicExponent Legendre.jZeroQuadraticBranch A

liftedJ1728MinusTwoFirstPoleDepthTwo :
  (A : LiftedDworkFirstPoleAuthority Legendre.j1728LambdaMinusTwo) →
  Ramified.valuation
    (Lift.valuation (localLift A))
    (Analytic.A1Coefficient
      (asA1Transfer Legendre.j1728LambdaMinusTwo A))
  ≡ 2
liftedJ1728MinusTwoFirstPoleDepthTwo A =
  liftedFirstPoleDepthIsAlgebraicExponent Legendre.j1728LambdaMinusTwo A

record DuncanSwisherDworkLiftedFirstPoleSharpnessBoundary : Set where
  field
    sameObjectPadicLiftRequired : Bool
    sameObjectPoleFamilyRequired : Bool
    firstPoleStoredIndependently : Bool
    ramificationExponentSourceOwned : Bool
    unitDepthsSourceOwned : Bool
    branchDepthSourceOwned : Bool
    numericA1DepthSourceOwned : Bool
    exactA1DepthDerived : Bool
    actualLiftConstructedHere : Bool
    actualDworkFamilyConstructedHere : Bool

canonicalDuncanSwisherDworkLiftedFirstPoleSharpnessBoundary :
  DuncanSwisherDworkLiftedFirstPoleSharpnessBoundary
canonicalDuncanSwisherDworkLiftedFirstPoleSharpnessBoundary = record
  { sameObjectPadicLiftRequired = true
  ; sameObjectPoleFamilyRequired = true
  ; firstPoleStoredIndependently = false
  ; ramificationExponentSourceOwned = false
  ; unitDepthsSourceOwned = false
  ; branchDepthSourceOwned = false
  ; numericA1DepthSourceOwned = false
  ; exactA1DepthDerived = true
  ; actualLiftConstructedHere = false
  ; actualDworkFamilyConstructedHere = false
  }

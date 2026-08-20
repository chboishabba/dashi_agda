module DASHI.Moonshine.DuncanSwisherDworkPublishedAnalyticCompletionExact where

------------------------------------------------------------------------
-- END-TO-END CLOSURE OF THE EXCEPTIONAL DWORK / LEGENDRE SOURCE CUTSET
--
-- PRIMARY SOURCES
--
-- Bernard Dwork, "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 and its proof.
--
-- Joseph H. Silverman, "The Arithmetic of Elliptic Curves", 2nd ed.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- DASHI CONTRIBUTION
--
-- Package the three formerly-outstanding source-facing objects without merging
-- their authorities:
--
--   (1) standard complete-DVR/Hensel Legendre local source;
--   (2) published Deligne--Dwork integer family A_n(alpha^) and its embedding;
--   (3) Dwork's deep p>3 n=1 sharpness theorem on THAT family.
--
-- From one package we CONSTRUCT:
--
--   lambda = lambda0 + pi,
--   lambda-lambda0 = pi*1,
--   the previous ExceptionalPadicLift,
--   the actual DworkPoleCoefficientFamily,
--   the old LiftedDworkFirstPoleAuthority,
--   and the target equality v_p(A_1)=v_p(J-alpha).
--
-- The target equality is not a field of this package.  It is derived by
-- composing the independent Dwork sharp value and Legendre ramification depth.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact as Lift
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel
import DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact as Pole
import DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact as Coeff
import DASHI.Moonshine.DuncanSwisherDworkPublishedFirstPoleSharpnessExact as Sharp
import DASHI.Moonshine.DuncanSwisherDworkLiftedFirstPoleSharpnessExact as Lifted

record PublishedExceptionalDworkAnalyticSource
    (branch : Legendre.ExceptionalLegendreBranch) : Set₁ where
  field
    localSource : Hensel.ExceptionalHenselLocalSource branch
    coefficientSource : Coeff.PublishedDworkCoefficientSource localSource
    primeGreaterThanThree : 4 ≤ Coeff.prime coefficientSource

open PublishedExceptionalDworkAnalyticSource public

actualPadicLift :
  (branch : Legendre.ExceptionalLegendreBranch) →
  PublishedExceptionalDworkAnalyticSource branch →
  Lift.ExceptionalPadicLift branch
actualPadicLift branch A =
  Hensel.constructExceptionalPadicLift branch (localSource A)

actualCoefficientFamily :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : PublishedExceptionalDworkAnalyticSource branch) →
  Pole.DworkPoleCoefficientFamily
actualCoefficientFamily branch A =
  Coeff.actualDworkPoleFamily (coefficientSource A)

actualFirstPole :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : PublishedExceptionalDworkAnalyticSource branch) →
  Hensel.PadicLocal (localSource A)
actualFirstPole branch A = Coeff.actualA1 (coefficientSource A)

actualLambdaMinusLambda0IsPiTimesOne :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : PublishedExceptionalDworkAnalyticSource branch) →
  Hensel.coordinateDifference (localSource A)
  ≡ Ramified.mul (Hensel.valuation (localSource A))
      (Hensel.uniformizer (localSource A))
      (Ramified.one (Hensel.valuation (localSource A)))
actualLambdaMinusLambda0IsPiTimesOne branch A =
  Hensel.coordinateDifferenceIsPiTimesOne (localSource A)

actualFirstPoleIsOrderOneFamilyMember :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : PublishedExceptionalDworkAnalyticSource branch) →
  actualFirstPole branch A
  ≡ Pole.poleCoefficient (actualCoefficientFamily branch A) (Pole.onePlus 0)
actualFirstPoleIsOrderOneFamilyMember branch A = refl

actualFirstPoleTracksLocalJ :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : PublishedExceptionalDworkAnalyticSource branch) →
  Ramified.valuation (Hensel.valuation (localSource A)) (actualFirstPole branch A)
  ≡ Ramified.valuation (Hensel.valuation (localSource A))
      (Lift.localJDifference (actualPadicLift branch A))
actualFirstPoleTracksLocalJ branch A =
  Sharp.publishedA1TracksConstructedLocalJDepth
    branch (localSource A) (coefficientSource A) (primeGreaterThanThree A)

actualFirstPoleDepthIsRamificationExponent :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : PublishedExceptionalDworkAnalyticSource branch) →
  Ramified.valuation (Hensel.valuation (localSource A)) (actualFirstPole branch A)
  ≡ Legendre.exceptionalRamificationExponent branch
actualFirstPoleDepthIsRamificationExponent branch A =
  Sharp.publishedDworkExceptionalFirstPoleSharpness
    (coefficientSource A) (primeGreaterThanThree A)

asFormerLiftedAuthority :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (A : PublishedExceptionalDworkAnalyticSource branch) →
  Lifted.LiftedDworkFirstPoleAuthority branch
asFormerLiftedAuthority branch A =
  Sharp.asLiftedDworkFirstPoleAuthority
    branch (localSource A) (coefficientSource A) (primeGreaterThanThree A)

record DuncanSwisherDworkPublishedAnalyticCompletionBoundary : Set where
  field
    actualPadicLiftConstructedFromHenselSource : Bool
    lambdaMinusLambda0PiUnitDerived : Bool
    actualRationalFunctionFactorsCarriedBySameLift : Bool
    actualAnFamilyConstructedOnSameCarrier : Bool
    A1DefinitionallyOrderOne : Bool
    deepN1SharpnessAttachedToActualFamily : Bool
    A1EqualsLocalJDepthDerivedNotImported : Bool
    formerLiftedAuthorityConstructed : Bool
    threeRequestedObjectsClosedAtPublishedSourceBoundaries : Bool
    fullDworkCyclesReproved : Bool

canonicalDuncanSwisherDworkPublishedAnalyticCompletionBoundary :
  DuncanSwisherDworkPublishedAnalyticCompletionBoundary
canonicalDuncanSwisherDworkPublishedAnalyticCompletionBoundary = record
  { actualPadicLiftConstructedFromHenselSource = true
  ; lambdaMinusLambda0PiUnitDerived = true
  ; actualRationalFunctionFactorsCarriedBySameLift = true
  ; actualAnFamilyConstructedOnSameCarrier = true
  ; A1DefinitionallyOrderOne = true
  ; deepN1SharpnessAttachedToActualFamily = true
  ; A1EqualsLocalJDepthDerivedNotImported = true
  ; formerLiftedAuthorityConstructed = true
  ; threeRequestedObjectsClosedAtPublishedSourceBoundaries = true
  ; fullDworkCyclesReproved = false
  }

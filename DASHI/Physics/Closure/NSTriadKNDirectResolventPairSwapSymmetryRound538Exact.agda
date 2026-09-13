module DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact where

------------------------------------------------------------------------
-- ROUND538 / THE LITERAL NONSEPARABLE RESOLVENT PAIR SCALAR IS SYMMETRIC
--
-- R406 enumerates unordered off-diagonal pairs.  To move that carrier toward a
-- swap-stable ordered square, first prove the actual scalar attached to a pair
-- is invariant under exchanging the two cells.
--
-- Define, before attaching any positivity proof,
--
--   F(alpha,beta)
--     = safeReciprocal(rate_alpha + rate_beta)
--         * nonlinearGramRemainder(alpha,beta).
--
-- The rate is symmetric by rational addition; the nonlinear remainder is
-- symmetric by real-Hermitian cross symmetry.  R384's positivity compiler then
-- stores exactly this scalar as R290.weightedNonlinearRemainder.  Positivity is
-- therefore authority for the reciprocal law, not a semantic coordinate of F.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive; _*_; _+_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

F : C3.RealField _
F = Rational.rationalRealField

module PairSwap
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module P = R389.DoubleMixedPair physicalSystem S

  Q : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → R291.DampedCellPair
  Q = P.physicalDoubleMixedPair

  pairRateSymmetric :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    R291.pairRate (Q alpha beta) ≡ R291.pairRate (Q beta alpha)
  pairRateSymmetric alpha beta =
    ℚP.+-comm (R291.rateA (Q alpha beta)) (R291.rateB (Q alpha beta))

  pairBracket :
    Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  pairBracket alpha beta =
    R291.nonlinearGramRemainder (Q alpha beta)

  pairBracketSymmetric :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairBracket alpha beta ≡ pairBracket beta alpha
  pairBracketSymmetric alpha beta =
    let
      qab = Q alpha beta
      leftToReverseSecond =
        R287.realHermitianCrossSymmetric
          (R291.forcingA qab) (R291.cellB qab)
      rightToReverseFirst =
        R287.realHermitianCrossSymmetric
          (R291.cellA qab) (R291.forcingB qab)
    in
    trans
      (cong (R291.two *_)
        (cong₂ _+_ leftToReverseSecond rightToReverseFirst))
      (cong (R291.two *_)
        (ℚP.+-comm
          (R179.realHermitianCross (R291.cellB qab) (R291.forcingA qab))
          (R179.realHermitianCross (R291.forcingB qab) (R291.cellA qab))))

  pairResolvent :
    Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  pairResolvent alpha beta =
    Reciprocal.safeRationalReciprocal (R291.pairRate (Q alpha beta))

  pairResolventSymmetric :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairResolvent alpha beta ≡ pairResolvent beta alpha
  pairResolventSymmetric alpha beta =
    cong Reciprocal.safeRationalReciprocal (pairRateSymmetric alpha beta)

  symmetricWeightedRemainder :
    Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  symmetricWeightedRemainder alpha beta =
    pairResolvent alpha beta * pairBracket alpha beta

  symmetricWeightedRemainderSwap :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    symmetricWeightedRemainder alpha beta
      ≡ symmetricWeightedRemainder beta alpha
  symmetricWeightedRemainderSwap alpha beta =
    cong₂ _*_
      (pairResolventSymmetric alpha beta)
      (pairBracketSymmetric alpha beta)

  literalR290WeightedRemainderIsSymmetricScalar :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (positive : Positive (R291.pairRate (Q alpha beta))) →
    R290.weightedNonlinearRemainder
      (P.pairRatePositiveBuildsR290 alpha beta positive)
    ≡ symmetricWeightedRemainder alpha beta
  literalR290WeightedRemainderIsSymmetricScalar alpha beta positive = refl

round538PairRateSymmetryClosed : Bool
round538PairRateSymmetryClosed = true

round538PairNonlinearRemainderSymmetryClosed : Bool
round538PairNonlinearRemainderSymmetryClosed = true

round538LiteralWeightedRemainderSymmetryClosed : Bool
round538LiteralWeightedRemainderSymmetryClosed = true

round538OrderedOffDiagonalConversionClosed : Bool
round538OrderedOffDiagonalConversionClosed = false

round538SignedSpacetimeEstimateClosed : Bool
round538SignedSpacetimeEstimateClosed = false

round538ClayPromotion : Bool
round538ClayPromotion = false

round538PairRateSymmetryClosedIsTrue : round538PairRateSymmetryClosed ≡ true
round538PairRateSymmetryClosedIsTrue = refl

round538LiteralWeightedRemainderSymmetryClosedIsTrue :
  round538LiteralWeightedRemainderSymmetryClosed ≡ true
round538LiteralWeightedRemainderSymmetryClosedIsTrue = refl

round538ClayPromotionIsFalse : round538ClayPromotion ≡ false
round538ClayPromotionIsFalse = refl

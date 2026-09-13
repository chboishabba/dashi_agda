module DASHI.Physics.Closure.NSTriadKNLiteralR396OrderedOffDiagonalRemainderRound540Exact where

------------------------------------------------------------------------
-- ROUND540 / LITERAL R396 R290 REMAINDER -> ORDERED OFF-DIAGONAL CARRIER
--
-- R538 proves that the proof-independent physical pair scalar F(alpha,beta)
-- equals each literal positive R290 weighted nonlinear remainder and is
-- symmetric under alpha<->beta.  R539 proves the generic finite identity
--
--   orderedOffDiagonal(F,xs) = 2 * unordered(F,xs).
--
-- This owner closes the same-object list-enumeration weld: R396's actual
-- positivity-indexed unordered R290 list sums exactly the same F.  Therefore
-- the live local remainder may be studied on the ordered off-diagonal carrier
-- without introducing any cardinality loss or analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539

F : C3.RealField _
F = Rational.rationalRealField

sumWeightedRemainderAppend :
  (left right : List R290.DampedGramPair) →
  R385.sumWeightedRemainder (left ++ right)
  ≡ R385.sumWeightedRemainder left + R385.sumWeightedRemainder right
sumWeightedRemainderAppend [] right = refl
sumWeightedRemainderAppend (pair ∷ rest) right
  rewrite sumWeightedRemainderAppend rest right = refl

module LiteralOrdered
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module E = R396.LocalEnumerate physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  headWeightedRemainderExact :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      R396._OccursIn_ beta rest →
      Positive (R291.pairRate (Swap.Q alpha beta))) →
    R385.sumWeightedRemainder (E.headR290Pairs alpha rest positive)
    ≡ R539.rowSum Swap.symmetricWeightedRemainder alpha rest
  headWeightedRemainderExact alpha [] positive = refl
  headWeightedRemainderExact alpha (beta ∷ rest) positive =
    cong₂ _+_
      (Swap.literalR290WeightedRemainderIsSymmetricScalar
        alpha beta (positive beta R396.here))
      (headWeightedRemainderExact alpha rest
        (λ gamma member → positive gamma (R396.there member)))

  allWeightedRemainderExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : E.PairRatePositiveOn items) →
    R385.sumWeightedRemainder (E.allR290Pairs items positive)
    ≡ R539.unorderedPairSum Swap.symmetricWeightedRemainder items
  allWeightedRemainderExact [] E.positiveNil = refl
  allWeightedRemainderExact
      (alpha ∷ rest) (E.positiveCons headPositive tailPositive) =
    trans
      (sumWeightedRemainderAppend
        (E.headR290Pairs alpha rest headPositive)
        (E.allR290Pairs rest tailPositive))
      (cong₂ _+_
        (headWeightedRemainderExact alpha rest headPositive)
        (allWeightedRemainderExact rest tailPositive))

  orderedOffDiagonalIsTwoLiteralWeightedRemainder :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : E.PairRatePositiveOn items) →
    R539.orderedOffDiagonalSum Swap.symmetricWeightedRemainder items
    ≡ R539.two * R385.sumWeightedRemainder (E.allR290Pairs items positive)
  orderedOffDiagonalIsTwoLiteralWeightedRemainder items positive =
    trans
      (R539.orderedOffDiagonalIsTwoUnordered
        Swap.symmetricWeightedRemainder
        Swap.symmetricWeightedRemainderSwap
        items)
      (cong₂ _*_
        refl
        (sym (allWeightedRemainderExact items positive)))

round540LiteralR396RemainderWeldClosed : Bool
round540LiteralR396RemainderWeldClosed = true

round540OrderedOffDiagonalRepresentationClosed : Bool
round540OrderedOffDiagonalRepresentationClosed = true

round540IntroducesCardinalityLoss : Bool
round540IntroducesCardinalityLoss = false

round540FullSquareCommutatorReductionClosed : Bool
round540FullSquareCommutatorReductionClosed = false

round540SignedSpacetimeEstimateClosed : Bool
round540SignedSpacetimeEstimateClosed = false

round540ClayPromotion : Bool
round540ClayPromotion = false

round540OrderedOffDiagonalRepresentationClosedIsTrue :
  round540OrderedOffDiagonalRepresentationClosed ≡ true
round540OrderedOffDiagonalRepresentationClosedIsTrue = refl

round540IntroducesCardinalityLossIsFalse :
  round540IntroducesCardinalityLoss ≡ false
round540IntroducesCardinalityLossIsFalse = refl

round540ClayPromotionIsFalse : round540ClayPromotion ≡ false
round540ClayPromotionIsFalse = refl

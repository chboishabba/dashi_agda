module DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact where

------------------------------------------------------------------------
-- ROUND497 / FINITE UNORDERED FIBRE SUM OF THE DIRECT RESOLVENT COMPANION
--
-- R396 enumerates each unordered list-position pair exactly once.  R496 proves
-- on every such physical pair that the literal R290 weighted nonlinear
-- remainder is exactly four times a direct nonseparable resolvent companion
-- contribution.  This file lifts that identity over the exact R396 list.
--
-- No integration, estimate, absolute value, Laplace factorization, or
-- cross-output coherence theorem appears here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; Positive)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496

F : C3.RealField _
F = Rational.rationalRealField

module DirectFibre
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Local = R396.LocalEnumerate physicalSystem S
  module Pair = R496.DirectPair physicalSystem S

  headCompanionSum :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive
        (R291.pairRate
          (Local.P.physicalDoubleMixedPair alpha beta))) →
    ℚ
  headCompanionSum alpha [] positive = 0ℚ
  headCompanionSum alpha (beta ∷ rest) positive =
    Pair.directResolventPairCompanion alpha beta (positive beta R396.here)
      + headCompanionSum alpha rest
          (λ gamma member → positive gamma (R396.there member))

  directFibreCompanion :
    (items : List Physical.PhysicalTriadIncidence) →
    Local.PairRatePositiveOn items → ℚ
  directFibreCompanion [] Local.positiveNil = 0ℚ
  directFibreCompanion (alpha ∷ rest)
      (Local.positiveCons headPositive tailPositive) =
    headCompanionSum alpha rest headPositive
      + directFibreCompanion rest tailPositive

  sumWeightedRemainderAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedRemainder (left ++ right)
    ≡ R385.sumWeightedRemainder left + R385.sumWeightedRemainder right
  sumWeightedRemainderAppend [] right = refl
  sumWeightedRemainderAppend (pair ∷ rest) right
    rewrite sumWeightedRemainderAppend rest right = refl

  headRemainderIsFourCompanion :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive
        (R291.pairRate
          (Local.P.physicalDoubleMixedPair alpha beta))) →
    R385.sumWeightedRemainder
      (Local.headR290Pairs alpha rest positive)
    ≡ R299.four * headCompanionSum alpha rest positive
  headRemainderIsFourCompanion alpha [] positive = solve []
  headRemainderIsFourCompanion alpha (beta ∷ rest) positive
      rewrite
        Pair.weightedRemainderIsFourDirectCompanion
          alpha beta (positive beta R396.here)
        | headRemainderIsFourCompanion alpha rest
            (λ gamma member → positive gamma (R396.there member)) =
    solve
      ( Pair.directResolventPairCompanion
          alpha beta (positive beta R396.here)
      ∷ headCompanionSum alpha rest
          (λ gamma member → positive gamma (R396.there member))
      ∷ [])

  allRemainderIsFourCompanion :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    R385.sumWeightedRemainder (Local.allR290Pairs items positive)
    ≡ R299.four * directFibreCompanion items positive
  allRemainderIsFourCompanion [] Local.positiveNil = solve []
  allRemainderIsFourCompanion (alpha ∷ rest)
      (Local.positiveCons headPositive tailPositive) =
    trans
      (sumWeightedRemainderAppend
        (Local.headR290Pairs alpha rest headPositive)
        (Local.allR290Pairs rest tailPositive))
      (trans
        (cong₂ _+_
          (headRemainderIsFourCompanion alpha rest headPositive)
          (allRemainderIsFourCompanion rest tailPositive))
        (solve
          ( headCompanionSum alpha rest headPositive
          ∷ directFibreCompanion rest tailPositive
          ∷ [])))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round497R396UnorderedPairEnumerationReused : Bool
round497R396UnorderedPairEnumerationReused = true

round497FiniteFibreRemainderIsFourDirectCompanionClosed : Bool
round497FiniteFibreRemainderIsFourDirectCompanionClosed = true

round497LaplaceRequired : Bool
round497LaplaceRequired = false

round497CrossOutputCoherenceRequired : Bool
round497CrossOutputCoherenceRequired = false

round497GlobalOutputAggregationClosed : Bool
round497GlobalOutputAggregationClosed = false

round497IntegratedCompanionWeldClosed : Bool
round497IntegratedCompanionWeldClosed = false

round497SignedSpacetimeEstimateClosed : Bool
round497SignedSpacetimeEstimateClosed = false

round497ClayPromotion : Bool
round497ClayPromotion = false

round497FiniteFibreRemainderIsFourDirectCompanionClosedIsTrue :
  round497FiniteFibreRemainderIsFourDirectCompanionClosed ≡ true
round497FiniteFibreRemainderIsFourDirectCompanionClosedIsTrue = refl

round497LaplaceRequiredIsFalse : round497LaplaceRequired ≡ false
round497LaplaceRequiredIsFalse = refl

round497ClayPromotionIsFalse : round497ClayPromotion ≡ false
round497ClayPromotionIsFalse = refl

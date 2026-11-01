module DASHI.Physics.Closure.NSTriadKNFixedOutputRateWeightedGramToR290Exact where

------------------------------------------------------------------------
-- FIXED-OUTPUT RATE-WEIGHTED GRAM ROW -> LITERAL R290 PAIR DYNAMICS
--
-- The physical coherent damping/covariance lane naturally produces the
-- off-diagonal scalar
--
--   sum_{alpha<beta} (rho_alpha + rho_beta)
--     W(D_alpha,D_beta).
--
-- R390 enumerates the SAME unordered double-mixed pairs as literal R290
-- DampedGramPair values.  On each such pair R291/R290 gives
--
--   g' = -(rho_alpha+rho_beta) g + R,
--
-- so, without any reciprocal or estimate,
--
--   (rho_alpha+rho_beta) g = R - g'.
--
-- This module proves the finite and literal-carrier versions of that identity.
-- It is the exact algebraic splice between the R229 variable-rate coherent
-- covariance and the R290/R503 Gram-flux lane.  It also makes the important
-- distinction explicit: the covariance contains PAIR-RATE-WEIGHTED Gram debt,
-- whereas the direct R503 normal form contains unweighted Gram debt.
--
-- No sign, norm, absolute value, cardinality bound, integration, or Clay
-- promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNLiteralGramDebtR290PairEnumerationRound390Exact as R390
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputRateWeightedGramRowDecompositionExact as Row

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Generic finite R290 identity.
------------------------------------------------------------------------

sumPairRateGram : List R290.DampedGramPair → ℚ
sumPairRateGram [] = 0ℚ
sumPairRateGram (pair ∷ rest) =
  R290.pairRate pair * R290.gram pair + sumPairRateGram rest

sumGramTangent : List R290.DampedGramPair → ℚ
sumGramTangent [] = 0ℚ
sumGramTangent (pair ∷ rest) =
  R290.gramTangent pair + sumGramTangent rest

sumNonlinearRemainder : List R290.DampedGramPair → ℚ
sumNonlinearRemainder [] = 0ℚ
sumNonlinearRemainder (pair ∷ rest) =
  R290.nonlinearRemainder pair + sumNonlinearRemainder rest

pairRateGramIsRemainderMinusTangent :
  (pair : R290.DampedGramPair) →
  R290.pairRate pair * R290.gram pair
  ≡ R290.nonlinearRemainder pair - R290.gramTangent pair
pairRateGramIsRemainderMinusTangent pair
  rewrite R290.tangentLaw pair =
  solve
    ( R290.pairRate pair
    ∷ R290.gram pair
    ∷ R290.nonlinearRemainder pair
    ∷ [])

finitePairRateGramIsRemainderMinusTangent :
  (pairs : List R290.DampedGramPair) →
  sumPairRateGram pairs
  ≡ sumNonlinearRemainder pairs - sumGramTangent pairs
finitePairRateGramIsRemainderMinusTangent [] = refl
finitePairRateGramIsRemainderMinusTangent (pair ∷ rest) =
  trans
    (cong₂ _+_
      (pairRateGramIsRemainderMinusTangent pair)
      (finitePairRateGramIsRemainderMinusTangent rest))
    (solve
      ( R290.nonlinearRemainder pair
      ∷ R290.gramTangent pair
      ∷ sumNonlinearRemainder rest
      ∷ sumGramTangent rest
      ∷ []))

------------------------------------------------------------------------
-- Literal R390 unordered-pair enumeration.
------------------------------------------------------------------------

module LiteralPairs
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (positivePairRate :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Positive
        (R291.pairRate
          (R389.DoubleMixedPair.physicalDoubleMixedPair
            physicalSystem S alpha beta))) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Enum = R390.Enumerate physicalSystem S positivePairRate

  rate : Physical.PhysicalTriadIncidence → ℚ
  rate = Pair.D.Pair.cellRate

  value : Physical.PhysicalTriadIncidence → C3.Complex3 F
  value = R225.doubleMixedCell S Pair.D.Pair.velocity

  sumPairRateGramAppend :
    (left right : List R290.DampedGramPair) →
    sumPairRateGram (Enum.append left right)
    ≡ sumPairRateGram left + sumPairRateGram right
  sumPairRateGramAppend [] right = refl
  sumPairRateGramAppend (pair ∷ rest) right
    rewrite sumPairRateGramAppend rest right = refl

  headPairsRateGramExact :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    sumPairRateGram (Enum.headR290Pairs alpha rest)
    ≡ Row.pairRateGramAgainstHead rate value alpha rest
  headPairsRateGramExact alpha [] = refl
  headPairsRateGramExact alpha (beta ∷ rest)
    rewrite headPairsRateGramExact alpha rest = refl

  allPairsRateGramExact :
    (items : List Physical.PhysicalTriadIncidence) →
    sumPairRateGram (Enum.allR290Pairs items)
    ≡ Row.pairRateOffDiagonalGram rate value items
  allPairsRateGramExact [] = refl
  allPairsRateGramExact (alpha ∷ rest) =
    trans
      (sumPairRateGramAppend
        (Enum.headR290Pairs alpha rest)
        (Enum.allR290Pairs rest))
      (cong₂ _+_
        (headPairsRateGramExact alpha rest)
        (allPairsRateGramExact rest))

  literalOffDiagonalRateGramIsR290RemainderMinusTangent :
    (items : List Physical.PhysicalTriadIncidence) →
    Row.pairRateOffDiagonalGram rate value items
    ≡
    sumNonlinearRemainder (Enum.allR290Pairs items)
      - sumGramTangent (Enum.allR290Pairs items)
  literalOffDiagonalRateGramIsR290RemainderMinusTangent items =
    trans
      (sym (allPairsRateGramExact items))
      (finitePairRateGramIsRemainderMinusTangent
        (Enum.allR290Pairs items))

------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

rateWeightedGramToR290PairDynamicsClosed : Bool
rateWeightedGramToR290PairDynamicsClosed = true

sameLiteralR390PairEnumerationUsed : Bool
sameLiteralR390PairEnumerationUsed = true

r229CovarianceEqualsUnweightedR503GramDebt : Bool
r229CovarianceEqualsUnweightedR503GramDebt = false

newAnalyticEstimateIntroduced : Bool
newAnalyticEstimateIntroduced = false

clayPromotion : Bool
clayPromotion = false

rateWeightedGramToR290PairDynamicsClosedIsTrue :
  rateWeightedGramToR290PairDynamicsClosed ≡ true
rateWeightedGramToR290PairDynamicsClosedIsTrue = refl

sameLiteralR390PairEnumerationUsedIsTrue :
  sameLiteralR390PairEnumerationUsed ≡ true
sameLiteralR390PairEnumerationUsedIsTrue = refl

r229CovarianceEqualsUnweightedR503GramDebtIsFalse :
  r229CovarianceEqualsUnweightedR503GramDebt ≡ false
r229CovarianceEqualsUnweightedR503GramDebtIsFalse = refl

newAnalyticEstimateIntroducedIsFalse :
  newAnalyticEstimateIntroduced ≡ false
newAnalyticEstimateIntroducedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

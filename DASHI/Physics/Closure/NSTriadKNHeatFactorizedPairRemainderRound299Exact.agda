module DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact where

------------------------------------------------------------------------
-- ROUND299 / FACTORIZE THE RESOLVENT PAIR REMAINDER BEFORE NORMS
--
-- R290/R291 leave the nonlinear part of a weighted Gram-pair tangent as two
-- Hermitian product-rule contributions.  Once the Cauchy resolvent weight is
-- represented by a one-cell Laplace/heat factor on each side, finite bilinear
-- aggregation has the schematic form
--
--   sum_{a,b} 2 Re <F_a,A_b> w_a w_b
-- + sum_{a,b} 2 Re <A_a,F_b> w_a w_b
--
-- = 4 Re < sum_a w_a A_a , sum_b w_b F_b >.
--
-- This module is the scalar compiler for that collapse.  It does NOT assert
-- the analytic Laplace identity 1/(lambda_a+lambda_b)=integral e^-s lambda_a
-- e^-s lambda_b ds.  The physical producer must identify its two finite
-- double-sum halves with the exact same heat-weighted aggregate cross term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

two four : ℚ
two = 2
four = 4

record HeatFactorizedPairRemainder : Set where
  constructor heat-factorized-pair-remainder
  field
    firstPairHalf secondPairHalf pairRemainder : ℚ
    aggregateAmplitudeForcingCross : ℚ

    pairRemainderSplits :
      pairRemainder ≡ firstPairHalf + secondPairHalf

    -- These are the SAME-OBJECT finite bilinear aggregation receipts.  The
    -- analytic heat/Laplace realization which manufactures the one-cell
    -- weights remains upstream and is intentionally not hidden here.
    firstHalfAggregates :
      firstPairHalf ≡ two * aggregateAmplitudeForcingCross

    secondHalfAggregates :
      secondPairHalf ≡ two * aggregateAmplitudeForcingCross

open HeatFactorizedPairRemainder public

pairRemainderIsFourTimesAggregateCross :
  (P : HeatFactorizedPairRemainder) →
  pairRemainder P ≡ four * aggregateAmplitudeForcingCross P
pairRemainderIsFourTimesAggregateCross P =
  trans
    (pairRemainderSplits P)
    (trans
      (cong₂ _+_ (firstHalfAggregates P) (secondHalfAggregates P))
      (solve (aggregateAmplitudeForcingCross P ∷ [])))

record PhysicalHeatFactorizedRemainderLeaf : Set where
  constructor physical-heat-factorized-remainder-leaf
  field
    factorizedPair : HeatFactorizedPairRemainder
    literalR291PairRemainderIsPairRemainder : Bool
    literalR291PairRemainderIsPairRemainderIsTrue :
      literalR291PairRemainderIsPairRemainder ≡ true
    r294SwapInvariantWeightUsedBeforeNorm : Bool
    r294SwapInvariantWeightUsedBeforeNormIsTrue :
      r294SwapInvariantWeightUsedBeforeNorm ≡ true

open PhysicalHeatFactorizedRemainderLeaf public

round299FinitePairFactorizationCompilerClosed : Bool
round299FinitePairFactorizationCompilerClosed = true

round299AnalyticLaplaceRepresentationInstalled : Bool
round299AnalyticLaplaceRepresentationInstalled = false

round299PhysicalDoubleSumSameObjectIdentificationInstalled : Bool
round299PhysicalDoubleSumSameObjectIdentificationInstalled = false

round299WeightedRemainderPaid : Bool
round299WeightedRemainderPaid = false

round299PackageAClosed : Bool
round299PackageAClosed = false

round299ClayPromotion : Bool
round299ClayPromotion = false

round299FinitePairFactorizationCompilerClosedIsTrue :
  round299FinitePairFactorizationCompilerClosed ≡ true
round299FinitePairFactorizationCompilerClosedIsTrue = refl

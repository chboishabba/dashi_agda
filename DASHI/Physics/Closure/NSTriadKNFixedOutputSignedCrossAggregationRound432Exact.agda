module DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact where

------------------------------------------------------------------------
-- ROUND432 / GLOBAL R406 REMAINDER REDUCES TO FIXED-OUTPUT COHERENCE
--
-- R398 constructs the live global R406 pair family by concatenating one
-- `outputPairs` list for each selected Fourier output.  Its theorem
-- `remainderAppend` is an exact identity:
--
--   remainder(left ++ right) = remainder(left) + remainder(right).
--
-- Therefore the R299 heat factorization may be performed fibre-by-fibre and
-- the resulting signed common crosses added afterwards.  There is NO
-- cross-output Gram/coherence theorem to prove.  All nontrivial coherence is
-- confined to one fixed output k.
--
-- This owner packages the corresponding scalar compiler.  If each fixed-output
-- signed cross C_k is bounded by a budget B_k, then
--
--   sum_k C_k <= sum_k B_k
--
-- with no factor equal to the number of outputs.  A cutoff-uniform theorem must
-- still pay the SUM of the fibre budgets by physical energy/dissipation or an
-- equivalent critical quantity; that is the remaining global step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398

record FixedOutputSignedCrossPayment : Set where
  constructor fixed-output-signed-cross-payment
  field
    signedCross fibreBudget : ℚ
    signedCrossBound : signedCross ≤ fibreBudget

open FixedOutputSignedCrossPayment public

sumSignedCross : List FixedOutputSignedCrossPayment → ℚ
sumSignedCross [] = 0ℚ
sumSignedCross (P ∷ rest) = signedCross P + sumSignedCross rest

sumFibreBudget : List FixedOutputSignedCrossPayment → ℚ
sumFibreBudget [] = 0ℚ
sumFibreBudget (P ∷ rest) = fibreBudget P + sumFibreBudget rest

fixedOutputBudgetsSumWithoutCardinalityFactor :
  (payments : List FixedOutputSignedCrossPayment) →
  sumSignedCross payments ≤ sumFibreBudget payments
fixedOutputBudgetsSumWithoutCardinalityFactor [] = ℚP.≤-refl
fixedOutputBudgetsSumWithoutCardinalityFactor (P ∷ rest) =
  ℚP.+-mono-≤
    (signedCrossBound P)
    (fixedOutputBudgetsSumWithoutCardinalityFactor rest)

record FixedOutputRemainderDecomposition : Set where
  constructor fixed-output-remainder-decomposition
  field
    payments : List FixedOutputSignedCrossPayment
    globalWeightedRemainder : ℚ
    globalRemainderIsFourFibreCrosses :
      globalWeightedRemainder ≡ R299.four * sumSignedCross payments

open FixedOutputRemainderDecomposition public

fixedOutputPaymentsBoundGlobalRemainder :
  (D : FixedOutputRemainderDecomposition) →
  globalWeightedRemainder D ≤ R299.four * sumFibreBudget (payments D)
fixedOutputPaymentsBoundGlobalRemainder D =
  let
    crossBound = fixedOutputBudgetsSumWithoutCardinalityFactor (payments D)
    fourNN : 0ℚ ≤ R299.four
    fourNN = ℚP.nonNegative⁻¹ R299.four
    scaled :
      R299.four * sumSignedCross (payments D)
      ≤ R299.four * sumFibreBudget (payments D)
    scaled =
      let instance fourNNI = Data.Rational.Base.nonNegative fourNN
      in ℚP.*-monoˡ-≤-nonNeg R299.four crossBound
  in
  subst
    (λ lower → lower ≤ R299.four * sumFibreBudget (payments D))
    (sym (globalRemainderIsFourFibreCrosses D))
    scaled

-- R398 is the same-object reason the live global pair family can be split by
-- output before applying R299.  This is not an abstract orthogonality claim.
round432R398GlobalPairsAreConcatenatedOutputFibres : Bool
round432R398GlobalPairsAreConcatenatedOutputFibres = true

round432R398RemainderAppendIsExact : Bool
round432R398RemainderAppendIsExact = R398.round398FiniteOutputAggregationClosed

round432CrossOutputCoherencePaymentRequired : Bool
round432CrossOutputCoherencePaymentRequired = false

round432OnlyFixedOutputCoherenceRemainsBeforeBudgetSummation : Bool
round432OnlyFixedOutputCoherenceRemainsBeforeBudgetSummation = true

round432FixedOutputBudgetSummationAddsCardinalityFactor : Bool
round432FixedOutputBudgetSummationAddsCardinalityFactor = false

round432CutoffUniformSumOfFibreBudgetsClosed : Bool
round432CutoffUniformSumOfFibreBudgetsClosed = false

round432R423SignedCommonCrossPaid : Bool
round432R423SignedCommonCrossPaid = false

round432PackageAClosed : Bool
round432PackageAClosed = false

round432ClayPromotion : Bool
round432ClayPromotion = false

round432CrossOutputCoherencePaymentRequiredIsFalse :
  round432CrossOutputCoherencePaymentRequired ≡ false
round432CrossOutputCoherencePaymentRequiredIsFalse = refl

round432OnlyFixedOutputCoherenceRemainsBeforeBudgetSummationIsTrue :
  round432OnlyFixedOutputCoherenceRemainsBeforeBudgetSummation ≡ true
round432OnlyFixedOutputCoherenceRemainsBeforeBudgetSummationIsTrue = refl

round432CutoffUniformSumOfFibreBudgetsClosedIsFalse :
  round432CutoffUniformSumOfFibreBudgetsClosed ≡ false
round432CutoffUniformSumOfFibreBudgetsClosedIsFalse = refl

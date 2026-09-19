{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4FiveChannelTaylorCauchyClosureExact where

------------------------------------------------------------------------
-- FIVE-CHANNEL TAYLOR CANCELLATION + CAUCHY COEFFICIENT MAJORANT
--   -> GLOBAL QUARTIC beta_int LOWER BOUND
--
-- The older physical frontier asked separately for
--
--   (i)  r_alpha(g) = g^4 q_alpha(g)
--   (ii) -c_alpha <= q_alpha(g).
--
-- Neither is primitive on this route anymore.
--
-- * BalabanYM4FiveChannelTaylorCancellationToFourthOrderExact derives (i)
--   from an actual expansion through cubic order and cancellation of the
--   coefficients 0,1,2,3.
--
-- * BalabanYM4FiveChannelCauchyQuotientMajorantExact derives (ii) from the
--   raw source coefficient estimate |a_n| <= A K^n, K|g|<1, geometric
--   summation, and standard order-closedness of the completed scalar limit.
--
-- This module composes the two.  The remaining physical analytic source work
-- is therefore exactly the literal Taylor/Cauchy representation and estimates,
-- not a direct O(g^4) or quotient-bound assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanYM4FiveChannelTaylorCancellationToFourthOrderExact as Taylor
import DASHI.Physics.YangMills.BalabanYM4FiveChannelCauchyQuotientMajorantExact as Cauchy
import DASHI.Physics.YangMills.BalabanYM4FiveChannelFourthOrderFactorizationExact as Fourth

record FiveChannelTaylorCauchyData (Cell : Set) : Set₁ where
  field
    taylor : Taylor.FiveChannelTaylorCancellationData Cell

    cauchy :
      Cell → Five.PhysicalBetaChannel → Cauchy.RawCompletedCauchyQuotient

    -- Same-object weld only: the completed Cauchy series is the exact quotient
    -- exposed by the Taylor cancellation theorem.
    cauchyLimitIsTaylorQuotient : ∀ cell channel →
      Cauchy.RawCompletedCauchyQuotient.quotient (cauchy cell channel)
      ≡ Taylor.fourthOrderQuotient taylor cell channel

open FiveChannelTaylorCauchyData public

asRawFiveChannelCauchyTailData :
  ∀ {Cell} →
  FiveChannelTaylorCauchyData Cell →
  Cauchy.RawFiveChannelCauchyTailData Cell
asRawFiveChannelCauchyTailData dataSet = record
  { Cauchy.RawFiveChannelCauchyTailData.cells =
      Taylor.cells (taylor dataSet)
  ; Cauchy.RawFiveChannelCauchyTailData.coupling =
      Taylor.coupling (taylor dataSet)
  ; Cauchy.RawFiveChannelCauchyTailData.channelRemainder =
      Taylor.channelRemainder (taylor dataSet)
  ; Cauchy.RawFiveChannelCauchyTailData.quotientData =
      cauchy dataSet
  ; Cauchy.RawFiveChannelCauchyTailData.exactFourthOrderFactorization =
      λ cell channel →
        trans
          (Taylor.exactFourthOrderFactorization
            (taylor dataSet) cell channel)
          (cong
            (λ quotient →
              Beta.power4 (Taylor.coupling (taylor dataSet)) * quotient)
            (sym (cauchyLimitIsTaylorQuotient dataSet cell channel)))
  }

asFourthOrderFactorizedFiveChannelData :
  ∀ {Cell} →
  FiveChannelTaylorCauchyData Cell →
  Fourth.FourthOrderFactorizedFiveChannelData Cell
asFourthOrderFactorizedFiveChannelData dataSet =
  Cauchy.asFourthOrderFactorizedFiveChannelData
    (Cauchy.rawAsFiveChannelCauchyTailData
      (asRawFiveChannelCauchyTailData dataSet))

taylorCauchyGlobalQuarticLower :
  ∀ {Cell} (dataSet : FiveChannelTaylorCauchyData Cell) →
  - (Five.coefficientTotal
      (Fourth.asFiveChannelQuarticBetaData
        (asFourthOrderFactorizedFiveChannelData dataSet))
      * Beta.power4 (Taylor.coupling (taylor dataSet)))
  ≤ Five.betaInt
      (Fourth.asFiveChannelQuarticBetaData
        (asFourthOrderFactorizedFiveChannelData dataSet))
taylorCauchyGlobalQuarticLower dataSet =
  Fourth.factorizedGlobalQuarticLower
    (asFourthOrderFactorizedFiveChannelData dataSet)

fiveChannelTaylorCauchyClosureLevel : ProofLevel
fiveChannelTaylorCauchyClosureLevel = machineChecked

-- Direct factorisation and direct quotient-majorant assumptions are eliminated
-- on this route.  These are the remaining literal source/analytic leaves.
literalFiveChannelTaylorExpansionThroughThirdOrderLevel : ProofLevel
literalFiveChannelTaylorExpansionThroughThirdOrderLevel =
  Taylor.physicalFiveChannelTaylorExpansionLevel

literalFiveChannelLowOrderCancellationLevel : ProofLevel
literalFiveChannelLowOrderCancellationLevel =
  Taylor.physicalFiveChannelLowOrderCancellationLevel

literalFiveChannelCauchyCoefficientEstimateLevel : ProofLevel
literalFiveChannelCauchyCoefficientEstimateLevel =
  Cauchy.literalFiveChannelCauchyCoefficientEstimateLevel

literalFiveChannelTaylorSeriesRepresentationLevel : ProofLevel
literalFiveChannelTaylorSeriesRepresentationLevel =
  Cauchy.literalFiveChannelTaylorSeriesRepresentationLevel

literalFiveChannelSeriesConvergenceLevel : ProofLevel
literalFiveChannelSeriesConvergenceLevel =
  Cauchy.literalFiveChannelSeriesConvergenceLevel

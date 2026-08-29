module DASHI.Physics.YangMills.BalabanChargeRelativeG2HeadroomAllocationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Round61 compresses the charge-relative canonical G2 scalar to
--
--   rawTotal + 2 E(B) (sourceTotal + defectTotal).
--
-- This file turns that exact identity into a non-overlapping headroom theorem.
-- Physical analysis may budget the raw and Green pieces independently; if the
-- two certified caps fit inside the final scalar gate, the actual canonical
-- residual ratio fits as well.
--
-- This is deliberately later than symmetry/Mobius/Schur reduction and earlier
-- than interval arithmetic.  It does not allow a bound on an unrelated axis to
-- discharge either physical component.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as GreenSchur
import DASHI.Physics.YangMills.BalabanChargeRelativeCanonicalSchurNormG2ClosureExact as Charge
import DASHI.Physics.YangMills.BalabanChargeRelativeG2AggregateRatioExact as Aggregate

------------------------------------------------------------------------
-- The exact Green correction which survives the sixteen-to-three compression.
------------------------------------------------------------------------

greenCorrectionAggregate :
  ∀ {Configuration Multiplier} →
  Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier → ℚ
greenCorrectionAggregate dataSet =
  (+ 2 / 1)
  * GreenSchur.energyCoefficient (Charge.rowBound dataSet)
  * (Aggregate.sourceNormRatioTotal dataSet
      + Aggregate.defectNormRatioTotal dataSet)

record G2AggregateHeadroom
    {Configuration Multiplier}
    (dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier)
    (target : ℚ) : Set where
  field
    rawBudget greenBudget : ℚ

    rawWithinBudget :
      Charge.rawRatioTotal dataSet ≤ rawBudget

    greenWithinBudget :
      greenCorrectionAggregate dataSet ≤ greenBudget

    budgetsFitTarget :
      rawBudget + greenBudget ≤ target

open G2AggregateHeadroom public

aggregateResidualWithinAllocatedHeadroom :
  ∀ {Configuration Multiplier target}
    {dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier} →
  G2AggregateHeadroom dataSet target →
  Aggregate.residualRatioAggregate dataSet ≤ target
aggregateResidualWithinAllocatedHeadroom {dataSet = dataSet} budget =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (rawWithinBudget budget)
      (greenWithinBudget budget))
    (budgetsFitTarget budget)

canonicalResidualWithinAllocatedHeadroom :
  ∀ {Configuration Multiplier target}
    {dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier} →
  G2AggregateHeadroom dataSet target →
  Charge.residualRatio dataSet ≤ target
canonicalResidualWithinAllocatedHeadroom {dataSet = dataSet} budget =
  subst
    (λ value → value ≤ _)
    (sym (Aggregate.residualRatioCollapsesToAggregateGate dataSet))
    (aggregateResidualWithinAllocatedHeadroom budget)

------------------------------------------------------------------------
-- The current physical scalar threshold.  The remaining physical producer can
-- now present one headroom allocation instead of sixteen signed Green bounds.
------------------------------------------------------------------------

canonicalG2Target : ℚ
canonicalG2Target = + 55 / 18874368

canonicalG2GateFromHeadroom :
  ∀ {Configuration Multiplier}
    {dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier} →
  G2AggregateHeadroom dataSet canonicalG2Target →
  Charge.residualRatio dataSet ≤ canonicalG2Target
canonicalG2GateFromHeadroom = canonicalResidualWithinAllocatedHeadroom

chargeRelativeG2HeadroomAllocationLevel : ProofLevel
chargeRelativeG2HeadroomAllocationLevel = machineChecked

-- Boundary: this theorem changes the shape of the remaining quantitative
-- obligation but does not fabricate the selected-region raw or Green bounds.
selectedRegionRawHeadroomProducerLevel : ProofLevel
selectedRegionRawHeadroomProducerLevel = conditional

selectedRegionGreenHeadroomProducerLevel : ProofLevel
selectedRegionGreenHeadroomProducerLevel = conditional

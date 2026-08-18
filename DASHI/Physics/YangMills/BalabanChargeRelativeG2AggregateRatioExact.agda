module DASHI.Physics.YangMills.BalabanChargeRelativeG2AggregateRatioExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proc. Cambridge Philosophical
-- Society 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- The Round60 charge-relative compiler still displayed sixteen Green ratios.
-- Their Schur endpoint is separable:
--
--   g(l,r) = -(1/2) E(B) (s_l + t_r).
--
-- Since there are exactly four Mobius degrees, finite algebra gives
--
--   sum_(l,r) g(l,r)
--     = -2 E(B) (sum_l s_l + sum_r t_r).
--
-- Hence the final G2 coefficient is exactly
--
--   residualRatio
--     = rawTotal + 2 E(B) (sourceTotal + defectTotal).
--
-- The physical producer therefore does not need sixteen Green constants, nor
-- even eight norm constants at the final comparison layer: only their two
-- aggregate sums, the four-raw aggregate, and the common pseudoinverse row
-- bound matter to the scalar gate.  Degreewise bounds remain useful upstream
-- as a sufficient way to establish those aggregates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as GreenSchur
import DASHI.Physics.YangMills.BalabanChargeRelativeCanonicalSchurNormG2ClosureExact as Charge

sourceNormRatioTotal :
  ∀ {Configuration Multiplier} →
  Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier → ℚ
sourceNormRatioTotal dataSet =
  Sums.sumRational Degree.allDegrees (Charge.sourceNormRatio dataSet)

defectNormRatioTotal :
  ∀ {Configuration Multiplier} →
  Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier → ℚ
defectNormRatioTotal dataSet =
  Sums.sumRational Degree.allDegrees (Charge.defectNormRatio dataSet)

greenRatioTotalAggregate :
  ∀ {Configuration Multiplier}
    (dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier) → ℚ
greenRatioTotalAggregate dataSet =
  - ((+ 2 / 1)
      * GreenSchur.energyCoefficient (Charge.rowBound dataSet)
      * (sourceNormRatioTotal dataSet + defectNormRatioTotal dataSet))

residualRatioAggregate :
  ∀ {Configuration Multiplier}
    (dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier) → ℚ
residualRatioAggregate dataSet =
  Charge.rawRatioTotal dataSet
  + (+ 2 / 1)
      * GreenSchur.energyCoefficient (Charge.rowBound dataSet)
      * (sourceNormRatioTotal dataSet + defectNormRatioTotal dataSet)

greenRatioTotalCollapsesToTwoAggregates :
  ∀ {Configuration Multiplier}
    (dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier) →
  Charge.greenRatioTotal dataSet ≡ greenRatioTotalAggregate dataSet
greenRatioTotalCollapsesToTwoAggregates dataSet =
  ℚRing.solve-∀
    (GreenSchur.energyCoefficient (Charge.rowBound dataSet))
    (Charge.sourceNormRatio dataSet Degree.degree1)
    (Charge.sourceNormRatio dataSet Degree.degree2)
    (Charge.sourceNormRatio dataSet Degree.degree3)
    (Charge.sourceNormRatio dataSet Degree.degree4)
    (Charge.defectNormRatio dataSet Degree.degree1)
    (Charge.defectNormRatio dataSet Degree.degree2)
    (Charge.defectNormRatio dataSet Degree.degree3)
    (Charge.defectNormRatio dataSet Degree.degree4)

residualRatioCollapsesToAggregateGate :
  ∀ {Configuration Multiplier}
    (dataSet : Charge.ChargeRelativeCanonicalG2Data Configuration Multiplier) →
  Charge.residualRatio dataSet ≡ residualRatioAggregate dataSet
residualRatioCollapsesToAggregateGate dataSet =
  trans
    (let
      collapsed = greenRatioTotalCollapsesToTwoAggregates dataSet
     in
      cong
        (λ green → Charge.rawRatioTotal dataSet - green)
        collapsed)
    (ℚRing.solve-∀
      (Charge.rawRatioTotal dataSet)
      (GreenSchur.energyCoefficient (Charge.rowBound dataSet))
      (sourceNormRatioTotal dataSet)
      (defectNormRatioTotal dataSet))
  where
  open import Relation.Binary.PropositionalEquality using (cong)

chargeRelativeG2SixteenGreenCompressionLevel : ProofLevel
chargeRelativeG2SixteenGreenCompressionLevel = machineChecked

chargeRelativeG2AggregateResidualGateLevel : ProofLevel
chargeRelativeG2AggregateResidualGateLevel = machineChecked

-- The remaining physical work is to prove the aggregate raw/source/defect
-- ratios and the common row bound strongly enough that this one scalar is at
-- most 55/18874368.  No separate sixteen-Green numerical producer remains.
selectedRegionAggregatePhysicalRatioLevel : ProofLevel
selectedRegionAggregatePhysicalRatioLevel = conditional

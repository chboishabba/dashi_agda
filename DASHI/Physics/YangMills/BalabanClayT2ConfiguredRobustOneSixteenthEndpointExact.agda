module DASHI.Physics.YangMills.BalabanClayT2ConfiguredRobustOneSixteenthEndpointExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredStrictLossMarginExact as Margin

------------------------------------------------------------------------
-- The old rational ledger used the coarse certificate log 16 <= 3 and thus
-- displayed zero rational slack.  The sharper positive-tail certificate proves
-- log 16 <= 14/5, leaving the exact tolerance 3 - 14/5 = 1/5.  This module
-- transports that tolerance into the physical activity endpoint.
------------------------------------------------------------------------

record RobustConfiguredActivityEndpoint
    (Scale Polymer Scalar : Set) : Set₁ where
  field
    robustness : Scale → Polymer → Margin.ConfiguredStrictLossRobustness Scalar

    activity factorProduct oneSixteenth : Scale → Polymer → Scalar

    LessEqual : Scalar → Scalar → Set
    orderAgrees : ∀ scale polymer left right →
      LessEqual left right
      ≡ Margin.LessEqual
          (Margin.analytic (robustness scale polymer)) left right

    activityBelowFactorProduct : ∀ scale polymer →
      LessEqual (activity scale polymer) (factorProduct scale polymer)

    robustNetGainImpliesFactorProductBelow : ∀ scale polymer →
      Margin.LessEqual (Margin.analytic (robustness scale polymer))
        (Margin.logarithm (Margin.analytic (robustness scale polymer))
          (Margin.rational (Margin.analytic (robustness scale polymer))
            Margin.sixteenℚ))
        (Margin.perturbedNetGain (robustness scale polymer)) →
      LessEqual (factorProduct scale polymer) (oneSixteenth scale polymer)

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

open RobustConfiguredActivityEndpoint public

literalWilsonActivityBelowOneSixteenthWithOneFifthRobustness :
  ∀ {Scale Polymer Scalar}
    (dataSet : RobustConfiguredActivityEndpoint Scale Polymer Scalar)
    scale polymer →
  LessEqual dataSet
    (activity dataSet scale polymer)
    (oneSixteenth dataSet scale polymer)
literalWilsonActivityBelowOneSixteenthWithOneFifthRobustness
  dataSet scale polymer =
  transitive dataSet
    (activityBelowFactorProduct dataSet scale polymer)
    (robustNetGainImpliesFactorProductBelow dataSet scale polymer
      (Margin.configuredPerturbedNetGainAtLeastLogSixteen
        (robustness dataSet scale polymer)))

configuredRobustActivityEndpointLevel : ProofLevel
configuredRobustActivityEndpointLevel = machineChecked

physicalAdditionalLossBelowOneFifthInputsLevel : ProofLevel
physicalAdditionalLossBelowOneFifthInputsLevel = conditional

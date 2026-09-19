module DASHI.Physics.YangMills.YMClayF3SprintConstructionFrontierValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayF3SprintConstructionFrontierExact as F3

samplingProjectionStillOpen :
  F3.sprint112SamplingMapConstructed ≡ false
samplingProjectionStillOpen = F3.sprint112SamplingStillOpen

interpolationStillOpen :
  F3.sprint112InterpolationMapConstructed ≡ false
interpolationStillOpen = F3.sprint112InterpolationStillOpen

unconditionalNormWindowStillOpen :
  F3.sprint116UnconditionalNormWindowClosed ≡ false
unconditionalNormWindowStillOpen = F3.sprint116NormWindowStillOpen

quotientGaugeAnalyticDischargeStillOpen :
  F3.sprint116QuotientGaugeAnalyticFeedsDischarged ≡ false
quotientGaugeAnalyticDischargeStillOpen = F3.sprint116QuotientGaugeStillOpen

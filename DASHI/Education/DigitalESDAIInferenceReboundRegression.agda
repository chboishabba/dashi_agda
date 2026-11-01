module DASHI.Education.DigitalESDAIInferenceReboundRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDAIInferenceScaleReboundExact as R
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

oviedoDOIRegression :
  Attr.AttributedSource.doiState R.oviedoInferenceEnergySource
  ≡ Attr.doiRecorded "10.1016/j.joule.2026.102430"
oviedoDOIRegression = refl

standardQueryMedianRegression : R.standardQueryMedianWh ≡ "0.31 Wh/query"
standardQueryMedianRegression = refl

longQueryMedianRegression : R.longQueryMedianWh ≡ "3.91 Wh/query"
longQueryMedianRegression = refl

aggregateScenarioRegression : R.oneBillionQueriesPerDayBaseline ≡ "0.7 GWh/day"
aggregateScenarioRegression = refl

reboundCeilingRegression :
  R.oviedoStrongestPaidImplication ≡ Cone.derivesBoundedContrast
reboundCeilingRegression = refl

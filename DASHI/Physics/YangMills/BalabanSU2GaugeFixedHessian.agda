module DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian where

record GaugeFixedHessianData (Fine Gauge Coarse : Set) : Set₁ where
  field
    wilsonHessian : Fine → Fine
    divergence : Fine → Gauge
    divergenceStar : Gauge → Fine
    average : Fine → Coarse
    averageStar : Coarse → Fine
    addFine : Fine → Fine → Fine

open GaugeFixedHessianData public

gaugePenalty :
  ∀ {Fine Gauge Coarse} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
gaugePenalty bundle fine = divergenceStar bundle (divergence bundle fine)

averagePenalty :
  ∀ {Fine Gauge Coarse} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
averagePenalty bundle fine = averageStar bundle (average bundle fine)

gaugeFixedHessian :
  ∀ {Fine Gauge Coarse} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
gaugeFixedHessian bundle fine =
  addFine bundle (wilsonHessian bundle fine)
    (addFine bundle (gaugePenalty bundle fine) (averagePenalty bundle fine))

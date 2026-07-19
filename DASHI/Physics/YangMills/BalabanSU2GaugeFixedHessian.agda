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
gaugePenalty data fine = divergenceStar data (divergence data fine)

averagePenalty :
  ∀ {Fine Gauge Coarse} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
averagePenalty data fine = averageStar data (average data fine)

gaugeFixedHessian :
  ∀ {Fine Gauge Coarse} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
gaugeFixedHessian data fine =
  addFine data (wilsonHessian data fine)
    (addFine data (gaugePenalty data fine) (averagePenalty data fine))

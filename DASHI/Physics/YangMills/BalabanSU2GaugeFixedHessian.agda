module DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian where

open import Agda.Primitive using (Level; _⊔_; lsuc)

record GaugeFixedHessianData
    {f g c : Level}
    (Fine : Set f) (Gauge : Set g) (Coarse : Set c)
    : Set (lsuc (f ⊔ g ⊔ c)) where
  field
    wilsonHessian : Fine → Fine
    divergence : Fine → Gauge
    divergenceStar : Gauge → Fine
    average : Fine → Coarse
    averageStar : Coarse → Fine
    addFine : Fine → Fine → Fine

open GaugeFixedHessianData public

gaugePenalty :
  ∀ {f g c} {Fine : Set f} {Gauge : Set g} {Coarse : Set c} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
gaugePenalty bundle fine = divergenceStar bundle (divergence bundle fine)

averagePenalty :
  ∀ {f g c} {Fine : Set f} {Gauge : Set g} {Coarse : Set c} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
averagePenalty bundle fine = averageStar bundle (average bundle fine)

gaugeFixedHessian :
  ∀ {f g c} {Fine : Set f} {Gauge : Set g} {Coarse : Set c} →
  GaugeFixedHessianData Fine Gauge Coarse → Fine → Fine
gaugeFixedHessian bundle fine =
  addFine bundle (wilsonHessian bundle fine)
    (addFine bundle (gaugePenalty bundle fine) (averagePenalty bundle fine))

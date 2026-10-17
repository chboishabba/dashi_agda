module DASHI.Biology.BH4FluxPaymentPreparationRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4FluxPaymentPreparationExact as Payment
import DASHI.Biology.BH4Phase4RoadmapExact as Roadmap

specificActivityIsNotCompartmentFlux :
  Payment.BH4FluxPaymentBoundary.specificActivityCreatesCompartmentFlux
    Payment.canonicalBH4FluxPaymentBoundary ≡ false
specificActivityIsNotCompartmentFlux = refl

kcatNeedsEnzymeAbundance :
  Payment.BH4FluxPaymentBoundary.kcatCreatesFluxWithoutAbundance
    Payment.canonicalBH4FluxPaymentBoundary ≡ false
kcatNeedsEnzymeAbundance = refl

kineticShapeDoesNotPayMagnitude :
  Payment.BH4FluxPaymentBoundary.shapeParameterCreatesMagnitudeBound
    Payment.canonicalBH4FluxPaymentBoundary ≡ false
kineticShapeDoesNotPayMagnitude = refl

primaryLiteratureDoesNotAutoPayFlux :
  Payment.BH4FluxPaymentBoundary.primaryLiteratureCreatesFluxBound
    Payment.canonicalBH4FluxPaymentBoundary ≡ false
primaryLiteratureDoesNotAutoPayFlux = refl

missingPaymentGateDefaultsFalse :
  Payment.BH4FluxPaymentBoundary.missingPaymentGateDefaultsPaid
    Payment.canonicalBH4FluxPaymentBoundary ≡ false
missingPaymentGateDefaultsFalse = refl

paymentPreparationToolIsReady : Roadmap.fluxPaymentPreparationToolReady ≡ true
paymentPreparationToolIsReady = refl

rankingToolRemainsReady : Roadmap.fluxCandidateRankingToolReady ≡ true
rankingToolRemainsReady = refl

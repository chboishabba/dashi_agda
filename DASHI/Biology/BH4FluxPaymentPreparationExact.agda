module DASHI.Biology.BH4FluxPaymentPreparationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

data BH4FluxEvidenceClass : Set where
  assaySpecificCapacity : BH4FluxEvidenceClass
  turnoverCapacity : BH4FluxEvidenceClass
  kineticShapeOnly : BH4FluxEvidenceClass
  primaryLiteratureGap : BH4FluxEvidenceClass

record BH4FluxPaymentBoundary : Set where
  constructor bh4-flux-payment-boundary
  field
    specificActivityCreatesCompartmentFlux : Bool
    specificActivityCreatesCompartmentFluxIsFalse : specificActivityCreatesCompartmentFlux ≡ false
    kcatCreatesFluxWithoutAbundance : Bool
    kcatCreatesFluxWithoutAbundanceIsFalse : kcatCreatesFluxWithoutAbundance ≡ false
    shapeParameterCreatesMagnitudeBound : Bool
    shapeParameterCreatesMagnitudeBoundIsFalse : shapeParameterCreatesMagnitudeBound ≡ false
    primaryLiteratureCreatesFluxBound : Bool
    primaryLiteratureCreatesFluxBoundIsFalse : primaryLiteratureCreatesFluxBound ≡ false
    missingPaymentGateDefaultsPaid : Bool
    missingPaymentGateDefaultsPaidIsFalse : missingPaymentGateDefaultsPaid ≡ false

open BH4FluxPaymentBoundary public

canonicalBH4FluxPaymentBoundary : BH4FluxPaymentBoundary
canonicalBH4FluxPaymentBoundary =
  bh4-flux-payment-boundary false refl false refl false refl false refl false refl

canonicalBH4FluxPaymentPreparationReceipt : Receipt.GenericReceipt
canonicalBH4FluxPaymentPreparationReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 reaction-flux payment preparation"
    "DASHI.Biology.BH4FluxPaymentPreparationExact"
    "ranked finite-reaction kinetics -> assay-specific capacity / turnover capacity / kinetic-shape-only / primary-literature-gap classes -> explicit normalization and context obligations"
    "prepares reaction-by-reaction quantitative payment without inventing intracellular flux bounds"
    "specific activity is not compartment flux; kcat needs enzyme abundance/state; Km/Kd/Ki do not set magnitude alone; primary literature does not auto-pay network flux; absent payment gates remain unpaid"
    "python3 scripts/prepare_bh4_flux_payment.py"

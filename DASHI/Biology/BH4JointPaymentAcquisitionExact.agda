module DASHI.Biology.BH4JointPaymentAcquisitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

record BH4JointPaymentAcquisitionBoundary : Set where
  constructor bh4-joint-payment-acquisition-boundary
  field
    proteinIntensityCreatesEnzymeConcentration : Bool
    proteinIntensityCreatesEnzymeConcentrationIsFalse : proteinIntensityCreatesEnzymeConcentration ≡ false
    metaboliteConcentrationCreatesExchangeFlux : Bool
    metaboliteConcentrationCreatesExchangeFluxIsFalse : metaboliteConcentrationCreatesExchangeFlux ≡ false
    sameObjectContextMayBeDropped : Bool
    sameObjectContextMayBeDroppedIsFalse : sameObjectContextMayBeDropped ≡ false
    contextCoverageCreatesSolverPayment : Bool
    contextCoverageCreatesSolverPaymentIsFalse : contextCoverageCreatesSolverPayment ≡ false
    proteinAbundanceCreatesReactionFlux : Bool
    proteinAbundanceCreatesReactionFluxIsFalse : proteinAbundanceCreatesReactionFlux ≡ false
    humanStudyOccurrenceCreatesTransportMechanism : Bool
    humanStudyOccurrenceCreatesTransportMechanismIsFalse : humanStudyOccurrenceCreatesTransportMechanism ≡ false

open BH4JointPaymentAcquisitionBoundary public

canonicalBH4JointPaymentAcquisitionBoundary : BH4JointPaymentAcquisitionBoundary
canonicalBH4JointPaymentAcquisitionBoundary =
  bh4-joint-payment-acquisition-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

canonicalBH4JointPaymentAcquisitionReceipt : Receipt.GenericReceipt
canonicalBH4JointPaymentAcquisitionReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 joint state/payment acquisition boundary"
    "DASHI.Biology.BH4JointPaymentAcquisitionExact"
    "exact UniProt panel -> ProteomicsDB abundance context; exact Rhea/ChEBI finite species -> RefMet/human-study context; both feed the existing 56-coordinate BH4 payment surface"
    "acquires missing context needed to adjudicate abundance-normalized reaction capacity and external exchange without inventing another flux calculus"
    "normalized protein intensity is not molar enzyme concentration; metabolite concentration/study occurrence is not transport flux; cross-tissue/context evidence is not one same-object state; context coverage never creates solver payment"
    "python3 scripts/run_bh4_phase4_maxcut.py"

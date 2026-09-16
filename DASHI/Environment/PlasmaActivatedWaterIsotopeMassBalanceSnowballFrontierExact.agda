module DASHI.Environment.PlasmaActivatedWaterIsotopeMassBalanceSnowballFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.PlasmaActivatedWaterSameObjectSnowballExact as SameObject

------------------------------------------------------------------------
-- PAW ISOTOPE / MASS-BALANCE SNOWBALL FRONTIER
--
-- Primary downstream studies can be retained now even when the first unpaid
-- isotope-recovery gate remains unresolved.  Publication-level continuity,
-- nutrient-content changes, root response and growth do not manufacture a
-- fertilizer-derived 15N recovery receipt.
------------------------------------------------------------------------

data PAWDownstreamPrimaryCarrier : Set where
  kizerArabidopsis2025
  kaushikMaizePea2024
  lettuceNitrogenRegime2026 : PAWDownstreamPrimaryCarrier

record PAWDownstreamSource : Set where
  constructor paw-downstream-source
  field
    carrier : PAWDownstreamPrimaryCarrier
    authors : String
    title : String
    year : Nat
    identifier : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open PAWDownstreamSource public

kizerSource : PAWDownstreamSource
kizerSource = paw-downstream-source
  kizerArabidopsis2025
  "Kizer et al."
  "Non-thermal plasma activated water is an effective nitrogen fertilizer alternative for Arabidopsis thaliana"
  2025
  "DOI 10.1371/journal.pone.0327091"
  "Same publication carries RF plasma production, PAW chemistry, nitrate-equivalent controls, root/transcriptomic responses and five-week plant outcomes."
  "Does not directly measure fertilizer-derived 15N recovery, instantaneous root-N flux, exact aliquot identity for every assay, field transport or lifecycle superiority."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

kaushikSource : PAWDownstreamSource
kaushikSource = paw-downstream-source
  kaushikMaizePea2024
  "Kaushik et al.; exact author list recoverable through DOI"
  "Investigating plasma activated water as a sustainable treatment for improving growth and nutrient uptake in maize and pea plant"
  2024
  "DOI 10.1016/j.plaphy.2024.109203"
  "Primary study combines atmospheric-pressure plasma diagnostics, PAW RONS/physicochemical measurements, maize/pea treatment and downstream nutrient-content/growth observations."
  "Nutrient-content change is not an isotope partition of PAW-derived N and does not prove field-scale N-use efficiency."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

lettuce2026Source : PAWDownstreamSource
lettuce2026Source = paw-downstream-source
  lettuceNitrogenRegime2026
  "authors recoverable through DOI"
  "Dual function of plasma-activated water in lettuce: growth promoter and nitrogen source under nitrogen-sufficient/-deprived conditions"
  2026
  "DOI 10.1016/j.scienta.2026.115042"
  "Primary lettuce hydroponic experiment separates nitrogen-sufficient and nitrogen-deprived regimes while evaluating PAW as nitrogen source and redox treatment."
  "Does not by itself identify fertilizer-derived 15N recovery, field transport, exact Kizer-batch identity or universal PAW replacement fraction."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

record PAWIsotopeAcquisitionState : Set where
  constructor paw-isotope-acquisition-state
  field
    sameObjectKizerCarrierAcquired : Bool
    maizePeaDiagnosticsOutcomeCarrierAcquired : Bool
    lettuceNitrogenRegimeCarrierAcquired : Bool
    reactorChemistryEvidenceAcquired : Bool
    plantGrowthEvidenceAcquired : Bool
    nutrientContentEvidenceAcquired : Bool
    rootMechanismEvidenceAcquired : Bool
    exactAliquotIdentityEvidenceAcquired : Bool
    isotopeLabelledPAWEvidenceAcquired : Bool
    fertilizerDerivedPlantNRecoveryEvidenceAcquired : Bool
    rootSoilResidualLossPartitionEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open PAWIsotopeAcquisitionState public

record PAWIsotopePaymentState : Set where
  constructor paw-isotope-payment-state
  field
    samePublicationCarrierPaid : Bool
    exactProductionBatchPaid : Bool
    exactChemistryApplicationAliquotPaid : Bool
    nitrogenLedgerPaid : Bool
    isotopeLabelIdentityPaid : Bool
    fertilizerDerivedPlantNRecoveryPaid : Bool
    soilResidualPAWNitrogenPaid : Bool
    PAWNitrogenLossPaid : Bool
    massBalanceClosurePaid : Bool
    SPACTransportPaid : Bool
    fieldTransportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open PAWIsotopePaymentState public

snowballAcquisitionDoesNotAdvancePAWIsotopePayment :
  PAWIsotopeAcquisitionState → PAWIsotopePaymentState → PAWIsotopePaymentState
snowballAcquisitionDoesNotAdvancePAWIsotopePayment _ payment = payment

record PAWIsotopeSearchResidual : Set where
  constructor paw-isotope-search-residual
  field
    searchQuestion : String
    exactRequiredCarrier : String
    currentlyLocatedPrimaryCarrier : String
    whyLocatedCarrierDoesNotPay : String
    residualStillOpen : Bool
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsResidualClassification : dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open PAWIsotopeSearchResidual public

canonicalIsotopeResidual : PAWIsotopeSearchResidual
canonicalIsotopeResidual = paw-isotope-search-residual
  "Is there a primary experiment using isotope-labelled PAW/fixed N to recover fertilizer-derived plant uptake, soil residual and loss from the same generated PAW carrier?"
  "reactor/batch identity + labelled-N chemistry + application + plant/soil recovery + loss/mass-balance receipts"
  "same-study PAW production/chemistry/plant carriers exist, including Kizer 2025, Kaushik 2024 and nitrogen-regime lettuce 2026"
  "none of these located carriers is promoted here to direct isotope-labelled PAW mass-balance recovery"
  true
  Attribution.dashiInferenceOwner
  refl

priorSameObjectBoundary : SameObject.SameObjectPAWBoundary
priorSameObjectBoundary = SameObject.canonicalSameObjectPAWBoundary

data NutrientContentMeansPAW15NRecovery : Set where
data GrowthMeansMassBalanceClosure : Set where
data SamePublicationMeansExactAliquot : Set where
data MultiplePrimaryStudiesMeanSameObject : Set where

nutrientContentDoesNotPayPAW15NRecovery : NutrientContentMeansPAW15NRecovery → ⊥
nutrientContentDoesNotPayPAW15NRecovery ()

growthDoesNotPayMassBalanceClosure : GrowthMeansMassBalanceClosure → ⊥
growthDoesNotPayMassBalanceClosure ()

samePublicationDoesNotPayExactAliquot : SamePublicationMeansExactAliquot → ⊥
samePublicationDoesNotPayExactAliquot ()

crossStudyEvidenceDoesNotCreateSameObject : MultiplePrimaryStudiesMeanSameObject → ⊥
crossStudyEvidenceDoesNotCreateSameObject ()

module DASHI.Wikimedia.IbrahimCannabisBtCannabisUseProductExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisBtBiopesticideExposureParetoExact as Bt
import DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact as Measurement
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- EXACT CANNABIS-USE Bt PRODUCT OWNERS
--
-- The previous Bt owner established that generic Bt registration does not pay
-- cannabis-use identity. This owner closes that gap with one California and
-- one Canadian product while retaining label, strain and formulation identity.
------------------------------------------------------------------------

record CannabisBtProductReceipt : Set where
  constructor cannabis-bt-product-receipt
  field
    jurisdiction : String
    productName : String
    registrationNumber : String
    organism : String
    strain : String
    formulationIdentity : String
    cannabisUseReference : String
    targetPestReference : String
    applicationRateReference : String
    timingReference : String
    preHarvestIntervalReference : String
    reentryReference : String
    exactCannabisUsePaid : Bool
    exactStrainPaid : Bool
    exactCryProteinComplementPaid : Bool
    postHarvestResiduePaid : Bool
open CannabisBtProductReceipt public

californiaDipelProDF : CannabisBtProductReceipt
californiaDipelProDF = cannabis-bt-product-receipt
  "California, USA"
  "DiPel Pro DF Biological Insecticide"
  "California DPR 73049-39-ZA; related EPA product 73049-39"
  "Bacillus thuringiensis subsp. kurstaki"
  "ABTS-351"
  "dry-flowable microbial insecticide; label active ingredient is ABTS-351 fermentation solids, spores and insecticidal toxins"
  "California DPR December 2024 assessed-product list marks DiPel Pro DF Y for legal cannabis-use criteria, with greenhouse/shadehouse/outdoor-nursery label compatibility; cannabis does not appear as a federal label crop"
  "listed caterpillar / lepidopteran larvae according to the product label"
  "label rates are crop/pest indexed; no cannabis-specific numeric rate is created here because California legality derives from state criteria plus compatible label directions"
  "treat young actively feeding larvae; repeat typically every 3-14 days according to monitoring and conditions"
  "label states no federal days-to-harvest restriction, subject to state requirements"
  "California product report carries label-specific worker/reentry precautions; no cannabis-specific REI is promoted here"
  true true true false

canadaBioprotecPlus : CannabisBtProductReceipt
canadaBioprotecPlus = cannabis-bt-product-receipt
  "Canada"
  "Bioprotec PLUS"
  "PMRA PCP 32425"
  "Bacillus thuringiensis subsp. kurstaki"
  "EVB113-19"
  "aqueous suspension; potency 17,500 cabbage-looper units per mg, equivalent to 20 billion CLU/L"
  "current PMRA label explicitly includes commercially indoor cannabis and field-grown cannabis"
  "commercially indoor cannabis: cabbage looper; field-grown cannabis/hemp: cabbage looper and European corn borer"
  "indoor cannabis cabbage looper: 1.1 L per 1000 L water; field-grown cannabis/hemp: 0.9-1.8 L/ha for cabbage looper and 1.8-2.5 L/ha for European corn borer"
  "indoor: begin just before egg hatch, then monitor; maximum 8 applications/year at 7-day intervals; field uses follow pest-specific monitoring/timing instructions"
  "0 days"
  "current Canadian crop-protection summaries report 4-hour general REI for Bioprotec PLUS; exact cannabis label wording remains product-label governed"
  true true false false

------------------------------------------------------------------------
-- ABTS-351 toxin/protein complement is independently source-resolved.
------------------------------------------------------------------------

record BtProteinComplementReceipt : Set where
  constructor bt-protein-complement-receipt
  field
    strain : String
    source : String
    geneOrProteinEvidence : String
    exactProductStrainJoinPaid : Bool
    residueOnCannabisPaid : Bool
open BtProteinComplementReceipt public

abts351ProteinComplement : BtProteinComplementReceipt
abts351ProteinComplement = bt-protein-complement-receipt
  "ABTS-351"
  "EFSA 2021 peer review plus 2020 proteomics of commercial Bt products"
  "ABTS-351 carries genes for Cry1Aa, Cry1Ab, Cry1Ac, Cry2Aa and Cry2Ab; proteomics directly identified Cry1Aa, Cry1Ab, Cry1Ac and Cry2Aa in DiPel DF, with weaker Cry2Ab evidence"
  true false

evb11319ProteinResidual : BtProteinComplementReceipt
evb11319ProteinResidual = bt-protein-complement-receipt
  "EVB113-19"
  "current PMRA/Canadian product labels pay strain identity and biological potency but the exact Cry/Vip protein complement was not source-resolved in this tranche"
  "unpaid: do not copy the ABTS-351 Cry complement onto EVB113-19 merely because both are Btk strains"
  true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameSubspeciesCreatesSameCryComplement : Set where
data ZeroDayPHICreatesZeroResidue : Set where
data LegalUseCreatesInhalationSafety : Set where
data ProductPotencyCreatesConsumerDose : Set where

sameSubspeciesDoesNotCreateSameCryComplement : SameSubspeciesCreatesSameCryComplement → ⊥
sameSubspeciesDoesNotCreateSameCryComplement ()

zeroDayPHIDoesNotCreateZeroResidue : ZeroDayPHICreatesZeroResidue → ⊥
zeroDayPHIDoesNotCreateZeroResidue ()

legalUseDoesNotCreateInhalationSafety : LegalUseCreatesInhalationSafety → ⊥
legalUseDoesNotCreateInhalationSafety ()

productPotencyDoesNotCreateConsumerDose : ProductPotencyCreatesConsumerDose → ⊥
productPotencyDoesNotCreateConsumerDose ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data BtProductParetoTarget : Set where
  measurePostApplicationFlowerBurden : BtProductParetoTarget
  resolveEVBProteinComplement : BtProductParetoTarget
  distinguishSporesFromCryProtein : BtProductParetoTarget
  combustionFate : BtProductParetoTarget
  vaporisationFate : BtProductParetoTarget
  inhaledDose : BtProductParetoTarget

record BtProductParetoStep : Set where
  constructor bt-product-pareto-step
  field
    priority : Nat
    target : BtProductParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open BtProductParetoStep public

pareto0 : BtProductParetoStep
pareto0 = bt-product-pareto-step
  0 measurePostApplicationFlowerBurden
  "find cannabis-flower data after a known Btk application measuring viable spores/CFU and/or Cry protein abundance at harvest"
  "source concentration for the biological residue consumer"
  "none"

pareto1 : BtProductParetoStep
pareto1 = bt-product-pareto-step
  1 resolveEVBProteinComplement
  "resolve EVB113-19 whole-genome or proteomic Cry/Vip complement instead of transferring ABTS-351 composition"
  "Canadian product toxin/protein identity"
  "strain identity is already paid"

pareto2 : BtProductParetoStep
pareto2 = bt-product-pareto-step
  2 distinguishSporesFromCryProtein
  "use separate observers for viable Btk burden and insecticidal protein burden in the same harvested-flower carrier"
  "biological-residue decomposition"
  "measurement methods must be matrix validated"

pareto3 : BtProductParetoStep
pareto3 = bt-product-pareto-step
  3 combustionFate
  "measure survival/degradation/transformation of spores and Cry proteins during smoking conditions"
  "combustion transfer packet"
  "source burden required first"

pareto4 : BtProductParetoStep
pareto4 = bt-product-pareto-step
  4 vaporisationFate
  "measure aerosol transfer separately under relevant vaporisation temperatures"
  "vaporisation transfer packet"
  "source burden required first"

pareto9 : BtProductParetoStep
pareto9 = bt-product-pareto-step
  9 inhaledDose
  "derive route-specific inhaled dose only after source burden and thermal-transfer fractions are measured"
  "consumer exposure admission"
  "dominated by residue and route-fate gaps"

------------------------------------------------------------------------
-- Temporal status.
------------------------------------------------------------------------

data BtProductTime : Set where
  genericBtState : BtProductTime
  cannabisUseProductsResolved : BtProductTime
  currentBtProductState : BtProductTime

data BtProductInterpretation : Set where
  exactCannabisUseProductsExist : BtProductInterpretation
  abts351CryComplementResolved : BtProductInterpretation
  evb11319CryComplementResolved : BtProductInterpretation
  harvestResidueResolved : BtProductInterpretation

data BtProductSummary : Set where cannabisBtIdentityPaidExposureOpen : BtProductSummary

BtProductCompatible : BtProductTime → BtProductInterpretation → Set
BtProductCompatible genericBtState exactCannabisUseProductsExist = ⊥
BtProductCompatible genericBtState abts351CryComplementResolved = ⊥
BtProductCompatible genericBtState evb11319CryComplementResolved = ⊥
BtProductCompatible genericBtState harvestResidueResolved = ⊥
BtProductCompatible cannabisUseProductsResolved exactCannabisUseProductsExist = ⊤
BtProductCompatible cannabisUseProductsResolved abts351CryComplementResolved = ⊤
BtProductCompatible cannabisUseProductsResolved evb11319CryComplementResolved = ⊥
BtProductCompatible cannabisUseProductsResolved harvestResidueResolved = ⊥
BtProductCompatible currentBtProductState exactCannabisUseProductsExist = ⊤
BtProductCompatible currentBtProductState abts351CryComplementResolved = ⊤
BtProductCompatible currentBtProductState evb11319CryComplementResolved = ⊥
BtProductCompatible currentBtProductState harvestResidueResolved = ⊥

btProductTemporalSystem : Temporal.TemporalEvidenceSystem
btProductTemporalSystem = record
  { Time = BtProductTime
  ; Interpretation = BtProductInterpretation
  ; Compatible = BtProductCompatible
  ; Summary = BtProductSummary
  ; summarize = λ _ → cannabisBtIdentityPaidExposureOpen
  ; timeReference = λ
      { genericBtState → "generic Bt product/regulatory state"
      ; cannabisUseProductsResolved → "California DiPel Pro DF and Canadian Bioprotec PLUS cannabis-use objects resolved"
      ; currentBtProductState → "current DASHI Bt product/exposure frontier"
      }
  }

currentBtProductResidual : Temporal.EvidenceFibre btProductTemporalSystem currentBtProductState
currentBtProductResidual = Temporal.liveInterpretationAt exactCannabisUseProductsExist tt

record CannabisBtProductBoundary : Set where
  constructor cannabis-bt-product-boundary
  field
    californiaCannabisUsePaid : Bool
    canadaCannabisUsePaid : Bool
    exactStrainsPaid : Bool
    abts351ProteinComplementPaid : Bool
    evb11319ProteinComplementPaid : Bool
    postHarvestResiduePaid : Bool
    zeroDayPhiMeansZeroResidue : Bool
open CannabisBtProductBoundary public

canonicalCannabisBtProductBoundary : CannabisBtProductBoundary
canonicalCannabisBtProductBoundary =
  cannabis-bt-product-boundary true true true true false false false

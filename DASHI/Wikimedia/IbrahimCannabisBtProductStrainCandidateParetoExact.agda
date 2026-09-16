module DASHI.Wikimedia.IbrahimCannabisBtProductStrainCandidateParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisBtBiopesticideExposureParetoExact as Bt
import DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact as Architecture

------------------------------------------------------------------------
-- BT PRODUCT / STRAIN CANDIDATE ARCHAEOLOGY
--
-- Pareto move after the measurement-architecture split: bind real registered
-- Bt product objects and strain identities, but do not promote any product to
-- cannabis-authorised use until the exact cannabis-use criteria/label join is
-- paid.
------------------------------------------------------------------------

record BtRegisteredProductCandidate : Set where
  constructor bt-registered-product-candidate
  field
    jurisdiction : String
    productName : String
    registrationNumber : String
    btIdentity : String
    activePercent : String
    formulationReference : String
    sourceReference : String
    currentlyRegistered : Bool
    exactCannabisUseAuthorised : Bool
    cryVipComplementPaid : Bool
open BtRegisteredProductCandidate public

javelinWGCalifornia : BtRegisteredProductCandidate
javelinWGCalifornia = bt-registered-product-candidate
  "California"
  "JAVELIN WG BIOLOGICAL INSECTICIDE"
  "70051-66-ZA"
  "Bacillus thuringiensis subsp. kurstaki; California DPR active-product registry"
  "exact active percentage/strain complement requires the selected product report/label join"
  "water-dispersible granule biological insecticide"
  "California DPR active-product search for Bacillus thuringiensis subsp. kurstaki"
  true false false

captainJacksBtCalifornia : BtRegisteredProductCandidate
captainJacksBtCalifornia = bt-registered-product-candidate
  "California"
  "CAPTAIN JACK'S BT BACILLUS THURINGIENSIS READY TO USE"
  "70051-113-ZA-4"
  "Bacillus thuringiensis subsp. kurstaki strain-family registry surface"
  "exact active percentage retained in product label rather than inferred from family search"
  "ready-to-use biological insecticide"
  "California DPR active-product search for B. thuringiensis subsp. kurstaki strain SA-family products"
  true false false

montereyBtCalifornia : BtRegisteredProductCandidate
montereyBtCalifornia = bt-registered-product-candidate
  "California"
  "MONTEREY B.T."
  "70051-106-AA-54705"
  "Bacillus thuringiensis subsp. kurstaki strain-family registry surface"
  "exact active percentage retained in product label rather than inferred from family search"
  "biological caterpillar-control product"
  "California DPR active-product search"
  true false false

thuricideCalifornia : BtRegisteredProductCandidate
thuricideCalifornia = bt-registered-product-candidate
  "California"
  "THURICIDE BACILLUS THURINGIENSIS (BT)"
  "4-226-ZA"
  "Bacillus thuringiensis subsp. kurstaki strain-family registry surface"
  "exact active percentage retained in product label rather than inferred from family search"
  "biological insecticide"
  "California DPR active-product search"
  true false false

sa12ProductExample : BtRegisteredProductCandidate
sa12ProductExample = bt-registered-product-candidate
  "California"
  "registered Bt product example with explicit SA-12 active"
  "product report 63068"
  "Bacillus thuringiensis subsp. kurstaki strain SA-12"
  "98.35% active; 1.65% inert ingredients"
  "product-report surface lists vegetables/fruits/tomato sites; cannabis site is not paid by this report"
  "California DPR Product Information Report 63068"
  true false false

abts351ProductExample : BtRegisteredProductCandidate
abts351ProductExample = bt-registered-product-candidate
  "California"
  "registered Bt product example with explicit ABTS-351 active"
  "product report 26760"
  "Bacillus thuringiensis subsp. kurstaki strain ABTS-351"
  "12.74% active; 87.26% inert ingredients"
  "product-report surface lists lettuce/tomato/vegetable/ornamental sites; cannabis site is not paid by this report"
  "California DPR Product Information Report 26760"
  true false false

------------------------------------------------------------------------
-- Regulatory join: exact registered product != cannabis-authorised product.
------------------------------------------------------------------------

record CannabisUseAdmission : Set where
  constructor cannabis-use-admission
  field
    productReference : String
    cannabisUseRuleReference : String
    labelSiteReference : String
    residueToleranceOrExemptionReference : String
    exactCurrentLabelReference : String
    exactProductMeetsCannabisCriteria : Bool
open CannabisUseAdmission public

currentCaliforniaBtCannabisResidual : CannabisUseAdmission
currentCaliforniaBtCannabisResidual = cannabis-use-admission
  "California DPR contains multiple currently registered Btk products"
  "California allows pesticide use on cannabis only when the active ingredients/product satisfy DPR cannabis-use criteria; DPR's public legal-use list is not exhaustive and is not an endorsement"
  "unpaid for the candidate products above: no exact cannabis-site or criteria join has yet been paid"
  "unpaid product-specific tolerance/exemption join"
  "unpaid exact current product label join"
  false

currentCanadaBtCannabisResidual : CannabisUseAdmission
currentCanadaBtCannabisResidual = cannabis-use-admission
  "Health Canada/PMRA product universe"
  "only pest control products registered or otherwise authorised specifically for cannabis may be used; label directions control"
  "unpaid: exact current Btk product/label returned by PMRA cannabis-site search"
  "unpaid"
  "unpaid"
  false

------------------------------------------------------------------------
-- Strain identity matters to the biological-residue consumer.
------------------------------------------------------------------------

data ProductFamilyCreatesStrainIdentity : Set where
data BtSpeciesNameCreatesCryComplement : Set where
data RegistrationCreatesCannabisAuthorisation : Set where
data ProductActivePercentCreatesFlowerResidue : Set where

productFamilyDoesNotCreateStrainIdentity : ProductFamilyCreatesStrainIdentity → ⊥
productFamilyDoesNotCreateStrainIdentity ()

btSpeciesNameDoesNotCreateCryComplement : BtSpeciesNameCreatesCryComplement → ⊥
btSpeciesNameDoesNotCreateCryComplement ()

registrationDoesNotCreateCannabisAuthorisation : RegistrationCreatesCannabisAuthorisation → ⊥
registrationDoesNotCreateCannabisAuthorisation ()

productActivePercentDoesNotCreateFlowerResidue : ProductActivePercentCreatesFlowerResidue → ⊥
productActivePercentDoesNotCreateFlowerResidue ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data BtProductParetoTarget : Set where
  exactCaliforniaCannabisBtProduct
  exactCanadaCannabisBtProduct
  exactLabelAndApplicationTiming
  strainAndCryVipComplement
  postApplicationFlowerResidue
  smokeVapeFate : BtProductParetoTarget

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
  0 exactCaliforniaCannabisBtProduct
  "resolve one currently registered Btk product through California's cannabis-use criteria/list or exact label path"
  "exact California cannabis-use product identity"
  "generic Btk registry search is insufficient"

pareto1 : BtProductParetoStep
pareto1 = bt-product-pareto-step
  1 exactCanadaCannabisBtProduct
  "query the current PMRA cannabis-use label universe for Btk and retain the exact registration/label if present"
  "independent cannabis-specific regulatory product object"
  "do not transfer California authorisation across jurisdiction"

pareto2 : BtProductParetoStep
pareto2 = bt-product-pareto-step
  2 exactLabelAndApplicationTiming
  "capture rate, target pest, application method, preharvest interval and flower-stage restrictions from the exact cannabis-use label"
  "exposure-generating application event definition"
  "exact authorised product required"

pareto3 : BtProductParetoStep
pareto3 = bt-product-pareto-step
  3 strainAndCryVipComplement
  "resolve the product strain and toxin/protein complement from regulatory or manufacturer primary evidence"
  "biological active identity"
  "product identity required"

pareto4 : BtProductParetoStep
pareto4 = bt-product-pareto-step
  4 postApplicationFlowerResidue
  "measure viable Bt and/or Cry/Vip protein on harvested cannabis flower after a specified application history"
  "source residue object"
  "application identity required"

pareto9 : BtProductParetoStep
pareto9 = bt-product-pareto-step
  9 smokeVapeFate
  "separate combustion and vaporisation survival/degradation/transfer only after source residue is paid"
  "consumer exposure bridge"
  "dominated by source-residue acquisition"

record BtProductCandidateBoundary : Set where
  constructor bt-product-candidate-boundary
  field
    realRegisteredProductsLocated : Bool
    explicitStrainExamplesLocated : Bool
    cannabisAuthorisationPaid : Bool
    cryVipComplementPaid : Bool
    harvestedFlowerResiduePaid : Bool
open BtProductCandidateBoundary public

canonicalBtProductCandidateBoundary : BtProductCandidateBoundary
canonicalBtProductCandidateBoundary =
  bt-product-candidate-boundary true true false false false

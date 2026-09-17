module DASHI.Biology.Agriculture.AcaciaSenegalDualSymbiosisPContextExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.AcaciaSenegalSymbiosisEnvironmentalEnablementExact as Enablement
import DASHI.Biology.Agriculture.AcaciaSenegalBNFEdaphicLESExact as Edaphic
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

------------------------------------------------------------------------
-- ACACIA/SENEGALIA DUAL-SYMBIOSIS + PHOSPHORUS CONTEXT
--
-- Rhizobial compatibility, AM-fungal state, plant-available P, nutrient
-- amendment and deployment environment are retained as separate coordinates.
-- This owner sharpens reaction-enablement context; it does not close the
-- canonical nitrogenase ladder.
------------------------------------------------------------------------

colonnaEtAl1991DOI : String
colonnaEtAl1991DOI = "10.1007/BF00205900"

yonliEtAl2022DOI : String
yonliEtAl2022DOI = "10.3389/fenvs.2022.803009"

colonnaEtAl1991 : Attribution.AttributedSource
colonnaEtAl1991 = Attribution.mkDOISource
  "J. P. Colonna; D. Thoen; M. Ducousso; S. Badji"
  "Comparative effects of Glomus mosseae and P fertilizer on foliar mineral composition of Acacia senegal seedlings inoculated with Rhizobium"
  "Mycorrhiza 1(1):35-38"
  "1991"
  colonnaEtAl1991DOI
  "https://doi.org/10.1007/BF00205900"
  Attribution.academicArticleSource
  "Greenhouse factorial source on degraded P-poor Dior soil comparing uninoculated, rhizobial, AM-fungal, dual-inoculation and rhizobium-plus-P treatments. Rhizobium alone was not sufficient to determine the strongest nodulation/growth/mineral-acquisition response; AM-fungal and especially added-P context changed the observed phenotype."
  Attribution.publicAttribution

yonliEtAl2022 : Attribution.AttributedSource
yonliEtAl2022 = Attribution.mkDOISource
  "Hendi Hermann Yonli; Godar Sene; Kadidia B. Sanon; Mahamadi Dianda; Damase P. Khasa"
  "Senegalia senegal (L.) Britton Response to Microbial and Manure Amendments for the Rehabilitation of Waste Rock Dumps in the Essakane Gold Mining Site, Burkina Faso"
  "Frontiers in Environmental Science 10:803009"
  "2022"
  yonliEtAl2022DOI
  "https://doi.org/10.3389/fenvs.2022.803009"
  Attribution.academicArticleSource
  "Nursery-plus-field restoration source crossing rhizobial/AM-fungal inoculation with manure amendment. High manure increased nursery growth but reduced nodulation/AM colonization; strongly colonized plants from lower-amendment contexts could show greater post-outplant survival. Nursery biomass, symbiosis establishment and field survival therefore remain distinct outcomes."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Source-bounded context receipts.
------------------------------------------------------------------------

data SymbiosisPartnerState : Set where
  rhizobiumOnly : SymbiosisPartnerState
  amfOnly : SymbiosisPartnerState
  rhizobiumAndAMF : SymbiosisPartnerState

data PhosphorusContext : Set where
  lowAvailableP : PhosphorusContext
  addedAvailableP : PhosphorusContext

data AmendmentContext : Set where
  noOrganicAmendment : AmendmentContext
  moderateOrganicAmendment : AmendmentContext
  highOrganicAmendment : AmendmentContext

data DeploymentPhase : Set where
  greenhouseNursery : DeploymentPhase
  postOutplantField : DeploymentPhase

record DualSymbiosisContextReceipt : Set where
  constructor dual-symbiosis-context-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    partnerReading : String
    phosphorusReading : String
    amendmentReading : String
    phaseReading : String
    noduleOrColonizationOutcome : String
    growthOutcome : String
    survivalOutcome : String
open DualSymbiosisContextReceipt public

colonnaFactorialReceipt : DualSymbiosisContextReceipt
colonnaFactorialReceipt = dual-symbiosis-context-receipt
  colonnaEtAl1991
  colonnaEtAl1991DOI
  "Rhizobium ORS1007, Glomus mosseae and dual-inoculation states compared"
  "Dior soil low in available P; rhizobium-plus-30/60 ppm P treatments retained separately"
  "soil sterilization/non-sterilization retained as microbial-background context"
  "greenhouse seedling experiment"
  "nodule dry mass changes substantially across partner/P treatments"
  "leaf/stem biomass responds strongly to partner/P context"
  "not a field-survival source"

yonliRestorationReceipt : DualSymbiosisContextReceipt
yonliRestorationReceipt = dual-symbiosis-context-receipt
  yonliEtAl2022
  yonliEtAl2022DOI
  "Mesorhizobium plurifarium ORS3588 crossed with native/exotic Rhizophagus inocula"
  "substrates differ in nutrient status; available-P state is not identified with a single total-P scalar"
  "0%, 25% and 50% manure-enriched substrate regimes"
  "nursery followed by waste-rock outplanting"
  "high manure can reduce nodulation and AM colonization despite greater nursery biomass"
  "nursery growth does not rank field-survival performance by itself"
  "post-outplant survival remains a distinct field outcome"

------------------------------------------------------------------------
-- Finite DASHI information-loss witness.
-- Synthetic worlds are calibrated by source-supported coordinate distinctions;
-- they are not additional empirical Acacia observations.
------------------------------------------------------------------------

data SymbiosisWorld : Set where
  compatibleRhizobiumLowP : SymbiosisWorld
  compatibleRhizobiumWithAMF : SymbiosisWorld
  compatibleRhizobiumAddedP : SymbiosisWorld

data PerformanceTask : Set where
  realisedSymbioticPerformanceTask : PerformanceTask

data RhizobialIdentity : Set where
  compatibleAcaciaRhizobium : RhizobialIdentity

rhizobialIdentityOnly : SymbiosisWorld → RhizobialIdentity
rhizobialIdentityOnly _ = compatibleAcaciaRhizobium

realisedSymbioticPerformance : PerformanceTask → SymbiosisWorld → Bool
realisedSymbioticPerformance realisedSymbioticPerformanceTask compatibleRhizobiumLowP = false
realisedSymbioticPerformance realisedSymbioticPerformanceTask compatibleRhizobiumWithAMF = true
realisedSymbioticPerformance realisedSymbioticPerformanceTask compatibleRhizobiumAddedP = true

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

rhizobialIdentityNotTaskSufficientAcrossPartnerAndPContext :
  LES.TaskFactorisation rhizobialIdentityOnly realisedSymbioticPerformance → ⊥
rhizobialIdentityNotTaskSufficientAcrossPartnerAndPContext factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor realisedSymbioticPerformanceTask
      {compatibleRhizobiumWithAMF} {compatibleRhizobiumLowP} refl)

------------------------------------------------------------------------
-- Existing context owners remain authoritative.
------------------------------------------------------------------------

environmentalEnablementBoundaryReused : Enablement.EnvironmentalEnablementBoundary
environmentalEnablementBoundaryReused = Enablement.canonicalEnvironmentalEnablementBoundary

edaphicBoundaryReused : Edaphic.AcaciaBNFEdaphicBoundary
edaphicBoundaryReused = Edaphic.canonicalEdaphicBoundary

reactionEnablementStillOpen :
  Chemistry.stageClosed Chemistry.reactionEnablement ≡ false
reactionEnablementStillOpen = Chemistry.reactionEnablementStillOpen

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record DualSymbiosisBoundary : Set where
  constructor dual-symbiosis-boundary
  field
    rhizobialIdentityAloneAdequateForRealisedPerformance : Bool
    availablePContextMayBeCollapsedToTotalP : Bool
    amfAndRhizobialStateMustRemainIndexed : Bool
    nutrientAmendmentMustRemainIndexed : Bool
    higherNutrientAmendmentImpliesBetterSymbiosis : Bool
    nurseryBiomassImpliesFieldSurvival : Bool
    noduleMassImpliesWholePlantFixedNDelivery : Bool
    greenhouseAndMineRestorationCreateSameEmpiricalObject : Bool
    sourceSpecificStrainsTransferAutomaticallyAcrossSites : Bool
    dualSymbiosisEvidenceClosesGenericReactionEnablement : Bool
    dualSymbiosisEvidenceCreatesDeploymentAuthority : Bool
open DualSymbiosisBoundary public

canonicalDualSymbiosisBoundary : DualSymbiosisBoundary
canonicalDualSymbiosisBoundary = dual-symbiosis-boundary
  false false true true false false false false false false false

attributionRule : String
attributionRule =
  "Colonna, Thoen, Ducousso & Badji 1991 (DOI 10.1007/BF00205900) owns its greenhouse Acacia-senegal Rhizobium/AMF/P-treatment propositions. Yonli, Sene, Sanon, Dianda & Khasa 2022 (DOI 10.3389/fenvs.2022.803009) owns its Senegalia-senegal microbial/manure nursery and waste-rock restoration propositions. DASHI owns only the context-indexed evidence carrier, synthetic information-loss witness and no-promotion boundary. The two papers are not fused into one empirical object; neither closes generic reaction enablement, whole-plant fixed-N delivery, fertilizer substitution or deployment authority."

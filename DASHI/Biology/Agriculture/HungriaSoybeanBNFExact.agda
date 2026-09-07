module DASHI.Biology.Agriculture.HungriaSoybeanBNFExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.Agriculture.HungriaBiologicalNitrogenFixationSourceAtlas as Sources
import DASHI.Core.SourceExactFrontierBidiCrossPollination2026 as SourceFrontier

------------------------------------------------------------------------
-- HUNGRIA / SOYBEAN BIOLOGICAL-NITROGEN-FIXATION SOURCE-EXACT SURFACE
--
-- Attribution discipline:
--
--   * empirical fields below are source-bounded representations of claims
--     reported by the cited external literature;
--   * the datatype decomposition, promotion boundaries, non-implications and
--     comparison calculus are DASHI formal reconstruction / synthesis;
--   * no DASHI theorem below is attributed to Hungria or her coauthors;
--   * the World Food Prize retrospective is not promoted into a primary-paper
--     experimental receipt.
------------------------------------------------------------------------

data Crop : Set where
  soybean : Crop
  maize : Crop
  wheat : Crop

data MicrobialRoute : Set where
  bradyrhizobiumSymbiosis : MicrobialRoute
  azospirillumAssociation : MicrobialRoute

data NitrogenOutcome : Set where
  fullSoybeanNitrogenSupplyReported : NitrogenOutcome
  improvedNitrogenNutritionReported : NitrogenOutcome
  noUniversalNitrogenReplacementClaim : NitrogenOutcome

data EvidenceScope : Set where
  fieldExperiment : EvidenceScope
  synthesis : EvidenceScope
  retrospective : EvidenceScope

record SourceBoundedBNFClaim : Set where
  constructor sourceBoundedClaim
  field
    crop : Crop
    route : MicrobialRoute
    nitrogenOutcome : NitrogenOutcome
    scope : EvidenceScope
    source : Sources.BNFSource
    universalAcrossCrops : Bool
    universalAcrossFarms : Bool
    exactCommercialCostComparisonEstablishedByThisSource : Bool

open SourceBoundedBNFClaim public

soybeanSynthesisClaim : SourceBoundedBNFClaim
soybeanSynthesisClaim =
  sourceBoundedClaim
    soybean
    bradyrhizobiumSymbiosis
    fullSoybeanNitrogenSupplyReported
    synthesis
    Sources.hungriaMendes2015
    false
    false
    false

soybeanPreInoculationClaim : SourceBoundedBNFClaim
soybeanPreInoculationClaim =
  sourceBoundedClaim
    soybean
    bradyrhizobiumSymbiosis
    improvedNitrogenNutritionReported
    fieldExperiment
    Sources.hungria2020
    false
    false
    false

maizeAzospirillumClaim : SourceBoundedBNFClaim
maizeAzospirillumClaim =
  sourceBoundedClaim
    maize
    azospirillumAssociation
    noUniversalNitrogenReplacementClaim
    fieldExperiment
    Sources.fukamiEtAl2016
    false
    false
    false

wheatAzospirillumClaim : SourceBoundedBNFClaim
wheatAzospirillumClaim =
  sourceBoundedClaim
    wheat
    azospirillumAssociation
    noUniversalNitrogenReplacementClaim
    fieldExperiment
    Sources.fukamiEtAl2016
    false
    false
    false

------------------------------------------------------------------------
-- Same-language firewall.
--
-- Social-media prose can flatten all three routes into "bacteria let crops
-- absorb nitrogen from the air".  The source-exact carrier keeps soybean
-- Bradyrhizobium symbiosis distinct from maize/wheat Azospirillum association.
------------------------------------------------------------------------

soybeanRouteNotMaizeRoute :
  route soybeanSynthesisClaim ≡ route maizeAzospirillumClaim → ⊥
soybeanRouteNotMaizeRoute ()

soybeanRouteNotWheatRoute :
  route soybeanSynthesisClaim ≡ route wheatAzospirillumClaim → ⊥
soybeanRouteNotWheatRoute ()

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

soybeanSynthesisNotUniversalAcrossCrops :
  universalAcrossCrops soybeanSynthesisClaim ≡ false
soybeanSynthesisNotUniversalAcrossCrops = refl

soybeanSynthesisNotUniversalAcrossFarms :
  universalAcrossFarms soybeanSynthesisClaim ≡ false
soybeanSynthesisNotUniversalAcrossFarms = refl

soybeanPaperDoesNotEstablishExactTwoVsFifty :
  exactCommercialCostComparisonEstablishedByThisSource soybeanSynthesisClaim ≡ false
soybeanPaperDoesNotEstablishExactTwoVsFifty = refl

preInoculationPaperDoesNotEstablishExactTwoVsFifty :
  exactCommercialCostComparisonEstablishedByThisSource soybeanPreInoculationClaim ≡ false
preInoculationPaperDoesNotEstablishExactTwoVsFifty = refl

maizePaperDoesNotEstablishUniversalReplacement :
  nitrogenOutcome maizeAzospirillumClaim ≡ noUniversalNitrogenReplacementClaim
maizePaperDoesNotEstablishUniversalReplacement = refl

wheatPaperDoesNotEstablishUniversalReplacement :
  nitrogenOutcome wheatAzospirillumClaim ≡ noUniversalNitrogenReplacementClaim
wheatPaperDoesNotEstablishUniversalReplacement = refl

------------------------------------------------------------------------
-- Source-stage boundary.
--
-- The institutional retrospective and the primary papers may concern the same
-- long-running research programme while remaining different evidence stages.
-- We deliberately reuse the generic SourceExact frontier: matching public
-- claim surfaces do not manufacture source-exactness or proof correspondence.
------------------------------------------------------------------------

sourceStageFirewall = SourceFrontier.announcementCannotRecoverSourceExactness

------------------------------------------------------------------------
-- DASHI-original decomposition of the viral claim.
--
-- A claim such as "$2 inoculant replaces $50 fertilizer and avoids X CO2" is
-- represented as a conjunction of independently sourced coordinates.  This is
-- not asserted to be a theorem of any one paper.
------------------------------------------------------------------------

data ViralClaimCoordinate : Set where
  biologicalMechanism : ViralClaimCoordinate
  soybeanNitrogenSubstitution : ViralClaimCoordinate
  treatmentCost : ViralClaimCoordinate
  fertilizerCounterfactualCost : ViralClaimCoordinate
  adoptionArea : ViralClaimCoordinate
  farmerSavings : ViralClaimCoordinate
  emissionsAvoided : ViralClaimCoordinate
  prizeAttribution : ViralClaimCoordinate

data ReceiptStage : Set where
  primaryExperimentalReceipt : ReceiptStage
  peerReviewedSynthesisReceipt : ReceiptStage
  institutionalEstimateReceipt : ReceiptStage
  prizeRecordReceipt : ReceiptStage
  notYetSameObjectWelded : ReceiptStage

coordinateStage : ViralClaimCoordinate → ReceiptStage
coordinateStage biologicalMechanism = peerReviewedSynthesisReceipt
coordinateStage soybeanNitrogenSubstitution = peerReviewedSynthesisReceipt
coordinateStage treatmentCost = institutionalEstimateReceipt
coordinateStage fertilizerCounterfactualCost = institutionalEstimateReceipt
coordinateStage adoptionArea = institutionalEstimateReceipt
coordinateStage farmerSavings = institutionalEstimateReceipt
coordinateStage emissionsAvoided = institutionalEstimateReceipt
coordinateStage prizeAttribution = prizeRecordReceipt

costStageNotPrimaryExperiment :
  coordinateStage treatmentCost ≡ primaryExperimentalReceipt → ⊥
costStageNotPrimaryExperiment ()

savingsStageNotPrimaryExperiment :
  coordinateStage farmerSavings ≡ primaryExperimentalReceipt → ⊥
savingsStageNotPrimaryExperiment ()

emissionsStageNotPrimaryExperiment :
  coordinateStage emissionsAvoided ≡ primaryExperimentalReceipt → ⊥
emissionsStageNotPrimaryExperiment ()

------------------------------------------------------------------------
-- Canonical conclusion.
--
-- The literature supports a strong, source-bounded soybean BNF result while
-- the viral economic/emissions sentence remains a cross-source synthesis whose
-- coordinates must retain their individual provenance.
------------------------------------------------------------------------

soybeanBNFSourceBounded : Bool
soybeanBNFSourceBounded = true

viralSentenceIsSinglePaperTheorem : Bool
viralSentenceIsSinglePaperTheorem = false

soybeanBNFSourceBoundedIsTrue : soybeanBNFSourceBounded ≡ true
soybeanBNFSourceBoundedIsTrue = refl

viralSentenceIsSinglePaperTheoremIsFalse :
  viralSentenceIsSinglePaperTheorem ≡ false
viralSentenceIsSinglePaperTheoremIsFalse = refl

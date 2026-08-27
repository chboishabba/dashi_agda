module DASHI.Governance.MithakaArchaeologicalEvidenceExact where

open import DASHI.Core.Prelude
import DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact as Sources

------------------------------------------------------------------------
-- MITHAKA COUNTRY: COLLABORATIVE ARCHAEOLOGICAL EVIDENCE
--
-- The Antiquity paper reports a Mithaka-initiated collaborative project with
-- numerous large stone quarries, grindstone-production evidence, substantial
-- dwellings and intensive regional economic practices.  It also explicitly
-- treats village settlement as an ongoing archaeological question: one set of
-- suspected hut foundations proved to be infilled quarry pits, while another
-- historically reported village locality yielded occupation evidence but no
-- surviving structures.
------------------------------------------------------------------------

data MithakaClaim : Set where
  largeScaleQuarrying
  grindstoneProduction
  substantialDwellings
  confirmedVillageSettlementAtAllTestedSites
  continentWideAgricultureClassification
  : MithakaClaim

data ClaimStatus : MithakaClaim → Set where
  evidencedQuarrying : ClaimStatus largeScaleQuarrying
  evidencedGrinding : ClaimStatus grindstoneProduction
  evidencedDwellings : ClaimStatus substantialDwellings
  villageStillOpen : ClaimStatus confirmedVillageSettlementAtAllTestedSites
  agricultureLabelNotSettled : ClaimStatus continentWideAgricultureClassification

source : Sources.SourceReference
source = Sources.mithakaAntiquity2021

record MithakaBoundary : Set where
  constructor mithakaBoundary
  field
    largeQuarriesImplyConfirmedVillageAtEverySite : Bool
    largeQuarriesImplyConfirmedVillageAtEverySiteIsFalse : largeQuarriesImplyConfirmedVillageAtEverySite ≡ false
    localEconomicEvidenceSettlesContinentWideTaxonomy : Bool
    localEconomicEvidenceSettlesContinentWideTaxonomyIsFalse : localEconomicEvidenceSettlesContinentWideTaxonomy ≡ false
    MithakaCollaborationTransfersAuthorityToPascoe : Bool
    MithakaCollaborationTransfersAuthorityToPascoeIsFalse : MithakaCollaborationTransfersAuthorityToPascoe ≡ false

canonicalMithakaBoundary : MithakaBoundary
canonicalMithakaBoundary = mithakaBoundary false refl false refl false refl

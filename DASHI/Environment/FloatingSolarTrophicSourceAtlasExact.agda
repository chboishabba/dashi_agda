module DASHI.Environment.FloatingSolarTrophicSourceAtlasExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- TROPHIC / NUTRIENT-FATE SOURCE ATLAS
--
-- This module deliberately keeps the nutrient-fate and IMTA evidence distinct
-- from the floating-solar biofouling paper.  It supplies external evidence for
-- LES questions about oyster-mediated biogeochemistry, harvest/export and
-- multi-trophic nutrient accounting; it does not promote those results into a
-- site-specific floating-solar prescription.
------------------------------------------------------------------------

record TrophicAttributedSource : Set where
  constructor trophic-attributed-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    stableIdentifier : String
    boundedClaim : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner
    ownerRemainsExternal : claimOwner ≡ Attribution.externalSourceOwner

open TrophicAttributedSource public

rayFulweiler2021DOI : String
rayFulweiler2021DOI = "10.1038/s41893-020-00644-9"

rayFulweiler2021 : TrophicAttributedSource
rayFulweiler2021 = trophic-attributed-source
  "Nicholas E. Ray; Robinson W. Fulweiler"
  "Meta-analysis of oyster impacts on coastal biogeochemistry"
  "Nature Sustainability 4 (2021) 261-269"
  2021
  "DOI 10.1038/s41893-020-00644-9"
  "Meta-analysis reports that oyster habitats can enhance excess-nitrogen removal through denitrification, alter nutrient recycling, and that reef and aquaculture configurations can have similar biogeochemical function at the level represented by the included studies."
  "A cross-study average does not establish a local clearance rate, local denitrification flux, carrying capacity, oxygen response, harvest export, or net water-quality benefit for a particular floating-solar installation."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

chambersEtAl2024DOI : String
chambersEtAl2024DOI = "10.1016/j.aquaculture.2024.740540"

chambersReportedNetNRemovalKg : String
chambersReportedNetNRemovalKg = "approximately 16.4 kg N"

chambersEtAl2024 : TrophicAttributedSource
chambersEtAl2024 = trophic-attributed-source
  "Michael Chambers; Michael Coogan; Michael Doherty; Hunt Howell"
  "Integrated multi-trophic aquaculture of steelhead trout, blue mussel and sugar kelp from a floating ocean platform"
  "Aquaculture 582 (2024) 740540"
  2024
  "DOI 10.1016/j.aquaculture.2024.740540"
  "A small-scale floating IMTA pilot cultured steelhead trout, blue mussels and sugar kelp. The study estimated 25.1 kg N released from trout production, 41.5 kg N extracted by mussels plus kelp, and approximately 16.4 kg net N removed from the ecosystem, with no observed negative local water-quality impact during the trial."
  "The pilot does not establish commercial-scale performance, generic open-water uptake efficiency, transferability to floating solar, absence of cumulative benthic loading, or universal environmental benefit."
  Attribution.primaryPublicationRecord Attribution.externalSourceOwner refl

------------------------------------------------------------------------
-- Explicit source-role separation.
------------------------------------------------------------------------

data FloatingSolarObservationCreatesNitrogenRemovalClaim : Set where
data OysterMetaAnalysisCreatesSiteSpecificFlux : Set where
data IMTAPilotCreatesFloatingSolarPrescription : Set where

open import Data.Empty using (⊥)

floatingSolarObservationDoesNotCreateNitrogenRemovalClaim :
  FloatingSolarObservationCreatesNitrogenRemovalClaim → ⊥
floatingSolarObservationDoesNotCreateNitrogenRemovalClaim ()

oysterMetaAnalysisDoesNotCreateSiteSpecificFlux :
  OysterMetaAnalysisCreatesSiteSpecificFlux → ⊥
oysterMetaAnalysisDoesNotCreateSiteSpecificFlux ()

imtaPilotDoesNotCreateFloatingSolarPrescription :
  IMTAPilotCreatesFloatingSolarPrescription → ⊥
imtaPilotDoesNotCreateFloatingSolarPrescription ()

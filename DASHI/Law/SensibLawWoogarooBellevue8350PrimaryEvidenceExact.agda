module DASHI.Law.SensibLawWoogarooBellevue8350PrimaryEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- BELLEVUE WOODS / EUGENE STREET EPBC 2018/8350 PRIMARY-EVIDENCE OWNER
--
-- Carries only propositions supported by the 2018/8350 referral package.
-- No proposition is transferred automatically to EPBC 2019/8575.
------------------------------------------------------------------------

record BellevuePrimaryCoordinate : Set where
  constructor bellevue-primary-coordinate
  field
    proposition : String
    sourceOwner : String
    provenanceStage : Provenance.LegalClaimProvenanceStage
    sameProjectAs20198575 : Bool
    transferableWithoutSameObjectWeld : Bool

open BellevuePrimaryCoordinate public

projectScale : BellevuePrimaryCoordinate
projectScale = bellevue-primary-coordinate
  "The Eugene Street / Bellevue project comprised a 33.8 ha site, an estimated 22.9 ha disturbance footprint, and about 21.2 ha of regulated/native vegetation clearing, with retention of the Woogaroo Creek riparian corridor."
  "EPBC 2018/8350 referral — CB Developments Pty Ltd / 28 South Environmental"
  Provenance.externalSourceClaim
  false false

koalaSignificance : BellevuePrimaryCoordinate
koalaSignificance = bellevue-primary-coordinate
  "The 2018/8350 proponent concluded the project was likely to have a significant impact on koala; approximately 21.3 ha of native vegetation scored 6 under the Koala Habitat Assessment Tool, characterised in the referral package as habitat critical to koala survival."
  "EPBC 2018/8350 MNES response / Attachment 17"
  Provenance.externalSourceClaim
  false false

corridorConnectivity : BellevuePrimaryCoordinate
corridorConnectivity = bellevue-primary-coordinate
  "The proponent described the site as part of a remnant-vegetation mosaic and described Woogaroo Creek as connective to larger remnant tracts to the south and to Brisbane River riparian habitat, with White Rock, Spring Mountain and Greenbank among the larger surrounding habitat tracts."
  "EPBC 2018/8350 referral environmental-condition/connectivity section"
  Provenance.externalSourceClaim
  false false

koalaLocalPopulation : BellevuePrimaryCoordinate
koalaLocalPopulation = bellevue-primary-coordinate
  "The proponent cited 71 Wildlife Online koala records within 1 km, survey evidence of koala use, and nearby Ric Nattrass and White Rock-Spring Mountain as notable koala locations, using those materials to argue significance of the site and surrounds to the local koala population."
  "EPBC 2018/8350 Attachment 17"
  Provenance.externalSourceClaim
  false false

restorationTimeLag : BellevuePrimaryCoordinate
restorationTimeLag = bellevue-primary-coordinate
  "The proponent stated that retaining remnant vegetation would help reduce lag time while ecological restoration established and that staged clearing could retain habitat for as long as possible subject to development progress."
  "EPBC 2018/8350 referral design-alternatives section"
  Provenance.externalSourceClaim
  false false

restorationHorizon : BellevuePrimaryCoordinate
restorationHorizon = bellevue-primary-coordinate
  "The proponent's koala outcomes used medium-term 10-year milestones for evidence of corridor use and a long-term 20+ year goal for a layered forest providing high-quality koala habitat."
  "EPBC 2018/8350 Table 4.2.1"
  Provenance.externalSourceClaim
  false false

------------------------------------------------------------------------
-- Gain/loss trade-off evidence from the proponent design history.
------------------------------------------------------------------------

record DesignTradeoff : Set where
  constructor design-tradeoff
  field
    proposition : String
    provenanceStage : Provenance.LegalClaimProvenanceStage
    provesImproperMotive : Bool
    provesLegalOutcomeFor20198575 : Bool

open DesignTradeoff public

yieldEcologyTradeoff : DesignTradeoff
yieldEcologyTradeoff = design-tradeoff
  "The referral records an initial maximum-yield concept of 395 lots, followed by design options losing 71 and 63 lots respectively to enlarge/open-space and buffering arrangements, before further ecological refinement; this is evidence that development yield and retained ecological space were explicit design trade-offs."
  Provenance.externalSourceClaim
  false false

engineeringConstraintTradeoff : DesignTradeoff
engineeringConstraintTradeoff = design-tradeoff
  "The referral states that engineering and stormwater requirements were an ultimate driver of road layout and stormwater design after ecological refinements."
  Provenance.externalSourceClaim
  false false

------------------------------------------------------------------------
-- Bounded cross-source inferences for the wider Woogaroo legal handoff.
------------------------------------------------------------------------

record BellevueInference : Set where
  constructor bellevue-inference
  field
    proposition : String
    stage : Provenance.LegalClaimProvenanceStage
    paidFor20198575 : Bool

existingVsRestoredInference : BellevueInference
existingVsRestoredInference = bellevue-inference
  "Within the same Woogaroo Creek landscape, the 2018/8350 proponent treated retained remnant habitat as immediately valuable and restoration as subject to multi-year/decadal lag; that is relevant comparative evidence when auditing claims that planted or restored offset habitat is functionally equivalent to existing mature connected habitat."
  Provenance.crossSourceInference
  false

cumulativeCorridorInference : BellevueInference
cumulativeCorridorInference = bellevue-inference
  "Because 2018/8350 itself describes Woogaroo Creek as a connective landscape feature, later project-by-project assessment of Springview, Scenic and Peninsular should test cumulative loss of the same corridor system rather than assume each project is ecologically isolated."
  Provenance.crossSourceInference
  false

record BellevueBoundary : Set where
  constructor bellevue-boundary
  field
    bellevueFactIsNotSpringviewFact : Bool
    proponentCriticalHabitatAssessmentIsNotAgencyFinding : Bool
    significantImpactIn8350DoesNotProveSignificantImpactIn8575 : Bool
    restorationLagEvidenceDoesNotAutomaticallyInvalidateOffset : Bool
    designYieldTradeoffDoesNotEstablishImproperMotive : Bool

bellevueBoundary : BellevueBoundary
bellevueBoundary = bellevue-boundary true true true true true

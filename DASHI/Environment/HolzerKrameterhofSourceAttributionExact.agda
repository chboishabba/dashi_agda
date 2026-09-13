module DASHI.Environment.HolzerKrameterhofSourceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- HOLZER / KRAMETERHOF SOURCE-ATTRIBUTION BOUNDARY
--
-- The user-supplied video transcript is admitted as a practitioner-report
-- source.  Statements made in the tour remain statements by the speaker under
-- that source context; they are not promoted to measured effect, causal proof,
-- universal design law or recommendation.
--
-- Official Krameterhof material is a separate institutional/farm-description
-- source.  DASHI owns the source taxonomy, cross-source synthesis and all
-- formal bridges/no-go results below.
------------------------------------------------------------------------

data KrameterhofSourceRole : Set where
  firstPersonFarmTour
  officialFarmDescription
  historicalPracticeLineage : KrameterhofSourceRole

data KrameterhofEvidenceRelation : Set where
  practitionerReportedPractice
  officialSiteMetadata
  historicalLineageOnly : KrameterhofEvidenceRelation

data KrameterhofEvidenceForm : Set where
  suppliedVideoTranscript
  officialWebsite
  existingTypedLineage : KrameterhofEvidenceForm

record KrameterhofSource : Set where
  constructor krameterhof-source
  field
    namedSpeakerOrInstitution : String
    titleOrDescription : String
    venueOrCarrier : String
    yearReference : String
    identifier : String
    role : KrameterhofSourceRole
    relation : KrameterhofEvidenceRelation
    evidenceForm : KrameterhofEvidenceForm
    boundedReading : String
    excludedPromotion : String
    claimOwner : Attribution.ClaimOwner

open KrameterhofSource public

josefHolzerSuppliedFarmTour : KrameterhofSource
josefHolzerSuppliedFarmTour = krameterhof-source
  "Josef Andreas Holzer (speaker identity supported by Krameterhof lineage/context; uploader authorship not asserted)"
  "Krameterhof farm tour: user-supplied transcript of YouTube video 5GMXqgQIU9c"
  "User-supplied transcript / YouTube carrier"
  "transcript supplied 2026-09-10; original upload date not asserted here"
  "https://www.youtube.com/watch?v=5GMXqgQIU9c"
  firstPersonFarmTour
  practitionerReportedPractice
  suppliedVideoTranscript
  "Practitioner-reported Krameterhof practices include terraced steep-slope farming, vertically cascaded ponds, gravity-fed water redistribution, mixed-depth pond habitat, fish/crayfish production, planted/rest ponds and open channels described as water-regeneration/re-oxygenation steps, adjustable standpipe pond levels, integrated terrace agroforestry, grazing livestock, rotational pigs and passive earth-cellar storage."
  "Does not by itself prove hydrologic efficiency, dissolved-oxygen improvement, water-quality restoration, erosion reduction, soil-carbon gain, livestock benefit, crop benefit, energy performance, transferability, safety, causal effect or universal permaculture efficacy."
  Attribution.externalSourceOwner

krameterhofOfficialFarmPage : KrameterhofSource
krameterhofOfficialFarmPage = krameterhof-source
  "Krameterhof / Josef Andreas Holzer"
  "Krameterhof farm and Holzer permaculture official site"
  "krameterhof.at"
  "accessed 2026-09-10"
  "https://krameterhof.at/en/krameterhof-farm/"
  officialFarmDescription
  officialSiteMetadata
  officialWebsite
  "Official farm description places Krameterhof on a steep Salzburg Lungau site of about 45 ha spanning roughly 1100-1500 m elevation and describes the farm as a diversified system; official lineage material states Josef Andreas Holzer took over further development in 2009."
  "Official operator metadata and practice description are not independent experimental validation or a causal effect estimate."
  Attribution.externalSourceOwner

holzerPermacultureLineage : KrameterhofSource
holzerPermacultureLineage = krameterhof-source
  "Krameterhof family/practice lineage"
  "Holzer permaculture historical lineage"
  "Krameterhof official lineage pages"
  "historical lineage; source consulted 2026-09-10"
  "https://krameterhof.at/en/what-ist-permaculture/why-holzer-permaculture/"
  historicalPracticeLineage
  historicalLineageOnly
  officialWebsite
  "Official lineage describes Sepp Holzer's earlier farm development and the later continuation by Josef Andreas Holzer; the lineage is retained as historical provenance rather than flattened into one author identity."
  "Does not make Sepp Holzer the speaker or author of Josef Holzer's later statements, and does not make Josef the inventor of every earlier practice in the lineage."
  Attribution.externalSourceOwner

canonicalKrameterhofSources : List KrameterhofSource
canonicalKrameterhofSources =
  josefHolzerSuppliedFarmTour ∷
  krameterhofOfficialFarmPage ∷
  holzerPermacultureLineage ∷ []

------------------------------------------------------------------------
-- Attribution / evidence non-laundering barriers.
------------------------------------------------------------------------

data PractitionerReportMeansMeasuredEffectPermission : Set where
data OfficialFarmPageMeansIndependentTrialPermission : Set where
data SeppLineageMeansJosefStatementAuthorshipPermission : Set where
data JosefStatementMeansSeppClaimPermission : Set where
data VideoCarrierMeansUploaderAuthorshipPermission : Set where
data PermacultureLabelMeansMechanismPermission : Set where
data PondOrTerraceMeansKeylineIdentityPermission : Set where

practitionerReportDoesNotBecomeMeasuredEffect :
  PractitionerReportMeansMeasuredEffectPermission → ⊥
practitionerReportDoesNotBecomeMeasuredEffect ()

officialOperatorPageDoesNotBecomeIndependentTrial :
  OfficialFarmPageMeansIndependentTrialPermission → ⊥
officialOperatorPageDoesNotBecomeIndependentTrial ()

seppLineageDoesNotOwnJosefStatements :
  SeppLineageMeansJosefStatementAuthorshipPermission → ⊥
seppLineageDoesNotOwnJosefStatements ()

josefStatementDoesNotBecomeSeppClaim :
  JosefStatementMeansSeppClaimPermission → ⊥
josefStatementDoesNotBecomeSeppClaim ()

videoCarrierDoesNotIdentifyUploaderAuthorship :
  VideoCarrierMeansUploaderAuthorshipPermission → ⊥
videoCarrierDoesNotIdentifyUploaderAuthorship ()

permacultureLabelDoesNotIdentifyMechanism :
  PermacultureLabelMeansMechanismPermission → ⊥
permacultureLabelDoesNotIdentifyMechanism ()

pondOrTerraceDoesNotMakeKeylineIdentity :
  PondOrTerraceMeansKeylineIdentityPermission → ⊥
pondOrTerraceDoesNotMakeKeylineIdentity ()

record KrameterhofAttributionBoundary : Set where
  constructor krameterhof-attribution-boundary
  field
    practitionerClaimAndMeasuredOutcomeRemainDistinct : Bool
    officialMetadataAndIndependentValidationRemainDistinct : Bool
    seppAndJosefAttributionRemainDistinct : Bool
    physicalTechniqueAndManagementLineageRemainDistinct : Bool
    dashiCrossSourceSynthesisRemainsDashiOwned : Bool
    unresolvedUploaderMetadataMayBeInvented : Bool

canonicalKrameterhofAttributionBoundary : KrameterhofAttributionBoundary
canonicalKrameterhofAttributionBoundary =
  krameterhof-attribution-boundary true true true true true false

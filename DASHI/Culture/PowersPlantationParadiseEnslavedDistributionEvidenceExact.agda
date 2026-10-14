module DASHI.Culture.PowersPlantationParadiseEnslavedDistributionEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.BenefitBurdenExternalityDistributionExact as Distribution

------------------------------------------------------------------------
-- ENSLAVED THEATRE DISTRIBUTION EVIDENCE
--
-- Julia Prest's 2023 monograph is used here at the bounded level exposed by
-- the publisher/author metadata and chapter structure: enslaved spectatorship,
-- theatre-maker slave ownership, and enslaved participation in theatre-making
-- are explicit study objects.  That pays category-level same-object evidence,
-- not complete actor-by-actor contribution/benefit/burden/voice incidence.
------------------------------------------------------------------------

prest2023EnslavedTheatreSource : Source.AttributedSource
prest2023EnslavedTheatreSource =
  Source.mkDOISource
    "Julia Tamsin Prest"
    "Public Theatre and the Enslaved People of Colonial Saint-Domingue"
    "Palgrave Macmillan"
    "2023"
    "10.1007/978-3-031-22691-5"
    "https://doi.org/10.1007/978-3-031-22691-5"
    Source.academicBookSource
    "book-length same-domain study whose published overview explicitly treats enslaved spectatorship, theatre-maker slave ownership and enslaved participation in theatre-making; bounded here to category-level evidence unless exact chapter passages or underlying records are separately inspected"
    Source.publicAttribution

data DistributionEvidenceAxis : Set where
  contributionAxis : DistributionEvidenceAxis
  benefitAxis : DistributionEvidenceAxis
  burdenAxis : DistributionEvidenceAxis
  voiceAxis : DistributionEvidenceAxis

data EvidenceGranularity : Set where
  categoryLevel : EvidenceGranularity
  actorVenueTimeLevel : EvidenceGranularity

record DistributionCategoryReceipt : Set where
  constructor distribution-category-receipt
  field
    axis : DistributionEvidenceAxis
    subjectClass : String
    historicalSurface : String
    source : Source.AttributedSource
    granularity : EvidenceGranularity
    actorLevelIncidenceComplete : Bool
    actorLevelIncidenceCompleteIsFalse :
      actorLevelIncidenceComplete ≡ false

open DistributionCategoryReceipt public

enslavedContributionCategoryReceipt : DistributionCategoryReceipt
enslavedContributionCategoryReceipt =
  distribution-category-receipt
    contributionAxis
    "enslaved people participating in theatre-making"
    "Prest's published overview and chapter structure explicitly identify concealed enslaved participation in theatre-making, including a dedicated contribution chapter"
    prest2023EnslavedTheatreSource
    categoryLevel
    false refl

enslavedBurdenCategoryReceipt : DistributionCategoryReceipt
enslavedBurdenCategoryReceipt =
  distribution-category-receipt
    burdenAxis
    "enslaved people connected to theatre-makers"
    "Prest's published chapter structure explicitly studies slave ownership among theatre directors, actors and instrumentalists, establishing theatre-making and enslavement as same-domain historical coordinates"
    prest2023EnslavedTheatreSource
    categoryLevel
    false refl

enslavedSpectatorshipCategoryReceipt : DistributionCategoryReceipt
enslavedSpectatorshipCategoryReceipt =
  distribution-category-receipt
    benefitAxis
    "enslaved people in or around the playhouse"
    "Prest's published chapter structure explicitly studies mitigated spectatorship by enslaved people; the category is therefore historically observable without assuming equal access or net benefit"
    prest2023EnslavedTheatreSource
    categoryLevel
    false refl

enslavedVoiceCategoryReceipt : DistributionCategoryReceipt
enslavedVoiceCategoryReceipt =
  distribution-category-receipt
    voiceAxis
    "enslaved people implicated in public theatre"
    "the monograph recovers hidden experiences through heterogeneous records, but the publisher-level surface does not itself pay actor-level agenda-setting, institutional voice or decision authority"
    prest2023EnslavedTheatreSource
    categoryLevel
    false refl

record EnslavedTheatreDistributionEvidence : Set where
  constructor enslaved-theatre-distribution-evidence
  field
    contributionReceipt : DistributionCategoryReceipt
    spectatorshipReceipt : DistributionCategoryReceipt
    burdenReceipt : DistributionCategoryReceipt
    voiceReceipt : DistributionCategoryReceipt
    genericDistributionBoundary : Distribution.BenefitBurdenExternalityBoundary
    actorVenueTimeJoinComplete : Bool
    actorVenueTimeJoinCompleteIsFalse : actorVenueTimeJoinComplete ≡ false

open EnslavedTheatreDistributionEvidence public

prest2023DistributionEvidence : EnslavedTheatreDistributionEvidence
prest2023DistributionEvidence =
  enslaved-theatre-distribution-evidence
    enslavedContributionCategoryReceipt
    enslavedSpectatorshipCategoryReceipt
    enslavedBurdenCategoryReceipt
    enslavedVoiceCategoryReceipt
    Distribution.canonicalBenefitBurdenExternalityBoundary
    false refl

data CategoryEvidenceCompletesDistributionalIncidence : Set where

categoryEvidenceDoesNotCompleteDistributionalIncidence :
  CategoryEvidenceCompletesDistributionalIncidence → ⊥
categoryEvidenceDoesNotCompleteDistributionalIncidence ()

record PowersEnslavedDistributionEvidenceBoundary : Set where
  constructor powers-enslaved-distribution-evidence-boundary
  field
    enslavedContributionCategoryPaid : Bool
    enslavedContributionCategoryPaidIsTrue :
      enslavedContributionCategoryPaid ≡ true
    theatreMakerOwnershipBurdenCategoryPaid : Bool
    theatreMakerOwnershipBurdenCategoryPaidIsTrue :
      theatreMakerOwnershipBurdenCategoryPaid ≡ true
    enslavedSpectatorshipCategoryPaid : Bool
    enslavedSpectatorshipCategoryPaidIsTrue :
      enslavedSpectatorshipCategoryPaid ≡ true
    actorLevelBenefitBurdenVoiceIncidenceComplete : Bool
    actorLevelBenefitBurdenVoiceIncidenceCompleteIsFalse :
      actorLevelBenefitBurdenVoiceIncidenceComplete ≡ false
    bookOverviewCreatesCausalEffect : Bool
    bookOverviewCreatesCausalEffectIsFalse :
      bookOverviewCreatesCausalEffect ≡ false

canonicalPowersEnslavedDistributionEvidenceBoundary :
  PowersEnslavedDistributionEvidenceBoundary
canonicalPowersEnslavedDistributionEvidenceBoundary =
  powers-enslaved-distribution-evidence-boundary
    true refl
    true refl
    true refl
    false refl
    false refl

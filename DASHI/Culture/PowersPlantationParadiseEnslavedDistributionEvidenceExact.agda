module DASHI.Culture.PowersPlantationParadiseEnslavedDistributionEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.BenefitBurdenExternalityDistributionExact as Distribution
import DASHI.Culture.PowersPlantationParadiseSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- ENSLAVED THEATRE DISTRIBUTION EVIDENCE
--
-- Julia Prest's 2023 monograph is used here at the bounded level exposed by
-- the publisher/author metadata and chapter structure: enslaved spectatorship,
-- theatre-maker slave ownership, and enslaved participation in theatre-making
-- are explicit study objects.  Laméca additionally preserves exact newspaper
-- coordinates for enslaved musicians tied to theatre work.  These payments do
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

------------------------------------------------------------------------
-- Named / actor-level contribution x coercive-status joins preserved by the
-- Laméca dossier from exact Affiches Américaines coordinates.  The original
-- newspaper images are not claimed inspected here.
------------------------------------------------------------------------

record EnslavedMusicianContributionBurdenReceipt : Set where
  constructor enslaved-musician-contribution-burden-receipt
  field
    personReference : String
    dateReference : String
    venueReference : String
    contributionReference : String
    burdenReference : String
    primaryCoordinate : String
    source : Source.AttributedSource
    primaryOriginalInspectedHere : Bool
    primaryOriginalInspectedHereIsFalse :
      primaryOriginalInspectedHere ≡ false
    contributionPaid : Bool
    contributionPaidIsTrue : contributionPaid ≡ true
    burdenPaid : Bool
    burdenPaidIsTrue : burdenPaid ≡ true
    benefitPaid : Bool
    benefitPaidIsFalse : benefitPaid ≡ false
    voicePaid : Bool
    voicePaidIsFalse : voicePaid ≡ false

open EnslavedMusicianContributionBurdenReceipt public

capViolinists1764ContributionBurdenReceipt :
  EnslavedMusicianContributionBurdenReceipt
capViolinists1764ContributionBurdenReceipt =
  enslaved-musician-contribution-burden-receipt
    "three young enslaved men offered for sale; two described as violinists able to read music"
    "15 February 1764"
    "Cap-Français theatre/opera circuit"
    "the two older musicians are reported as having accompanied different operas performed at Le Cap during the preceding two years"
    "the same advertisement presents the young men as saleable enslaved property"
    "Affiches Américaines, Le Cap, 15 February 1764"
    Atlas.lamecaSaintDomingueOperaSource
    false refl
    true refl
    true refl
    false refl
    false refl

julien1781ContributionBurdenReceipt :
  EnslavedMusicianContributionBurdenReceipt
julien1781ContributionBurdenReceipt =
  enslaved-musician-contribution-burden-receipt
    "Julien, described in the source with the colonial racial term 'jeune griffe', age about 17-18"
    "13 November 1781"
    "Comédie du Cap"
    "viola player reported as engaged at the Cap theatre until Easter"
    "the same source coordinate is a sale notice, joining theatre labour to enslaved sale status on the same person"
    "Affiches Américaines, Le Cap, 13 November 1781"
    Atlas.lamecaSaintDomingueOperaSource
    false refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Aggregate/category packet.
------------------------------------------------------------------------

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

data ContributionBurdenJoinCompletesBenefitVoice : Set where

contributionBurdenJoinDoesNotCompleteBenefitVoice :
  ContributionBurdenJoinCompletesBenefitVoice → ⊥
contributionBurdenJoinDoesNotCompleteBenefitVoice ()

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
    namedContributionBurdenJoinPartiallyPaid : Bool
    namedContributionBurdenJoinPartiallyPaidIsTrue :
      namedContributionBurdenJoinPartiallyPaid ≡ true
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
    true refl
    false refl
    false refl

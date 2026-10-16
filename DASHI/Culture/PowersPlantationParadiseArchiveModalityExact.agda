module DASHI.Culture.PowersPlantationParadiseArchiveModalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.PowersPlantationParadiseMethodologySourceAtlasExact as Methodology

------------------------------------------------------------------------
-- ARCHIVE MODALITY / SOURCE-GENERATING PROCESS
--
-- A historical source is not only a proposition carrier.  Genre, producer,
-- institutional setting and intended function affect what the source is likely
-- to record or omit.  These coordinates constrain interpretation; they do not
-- create historical truth.
------------------------------------------------------------------------

data SourceGenre : Set where
  theatreAnnouncement : SourceGenre
  runawaySaleAdvertisement : SourceGenre
  notarialWill : SourceGenre
  policeOrTheatreRule : SourceGenre
  courtOrLegalRecord : SourceGenre
  architecturalPlan : SourceGenre
  retrospectiveNarrative : SourceGenre

data SourceProducerClass : Set where
  theatrePublicist : SourceProducerClass
  enslaverOrSeller : SourceProducerClass
  notaryOrTestator : SourceProducerClass
  colonialAuthority : SourceProducerClass
  courtOfficial : SourceProducerClass
  architectOrSurveyor : SourceProducerClass
  retrospectiveAuthor : SourceProducerClass

data SourcePurposeClass : Set where
  advertiseAttendance : SourcePurposeClass
  recoverOrTransferProperty : SourcePurposeClass
  recordObligationOrDisposition : SourcePurposeClass
  regulateConductOrAccess : SourcePurposeClass
  recordProceedingOrDispute : SourcePurposeClass
  recordSpatialConfiguration : SourcePurposeClass
  narrateOrDescribe : SourcePurposeClass

record SourceProductionContext : Set where
  constructor source-production-context
  field
    genre : SourceGenre
    producerClass : SourceProducerClass
    purposeClass : SourcePurposeClass
    likelyRichCoordinate : String
    likelySilentCoordinate : String
    coerciveProductionContext : Bool
    historicalTruthProducedByGenre : Bool
    historicalTruthProducedByGenreIsFalse :
      historicalTruthProducedByGenre ≡ false

open SourceProductionContext public

runawaySaleAdvertisementContext : SourceProductionContext
runawaySaleAdvertisementContext =
  source-production-context
    runawaySaleAdvertisement
    enslaverOrSeller
    recoverOrTransferProperty
    "bodily description, skill, mobility, ownership/sale coordinates may be unusually visible"
    "subject voice, consent and self-description may be absent or distorted by the coercive producer"
    true
    false refl

theatreAnnouncementContext : SourceProductionContext
theatreAnnouncementContext =
  source-production-context
    theatreAnnouncement
    theatrePublicist
    advertiseAttendance
    "date, venue, repertoire, performer billing and benefit framing may be visible"
    "labour relation, backstage contribution, coercive status and realised net benefit may be omitted"
    false
    false refl

notarialWillContext : SourceProductionContext
notarialWillContext =
  source-production-context
    notarialWill
    notaryOrTestator
    recordObligationOrDisposition
    "contracts, arrears, property, obligations and intended estate dispositions may be visible"
    "actual downstream settlement may remain unproved without executor/account records"
    false
    false refl

policeRuleContext : SourceProductionContext
policeRuleContext =
  source-production-context
    policeOrTheatreRule
    colonialAuthority
    regulateConductOrAccess
    "formal permission, prohibition, seating, pricing or enforcement rule may be visible"
    "realised practice and informal evasion may remain distinct"
    false
    false refl

------------------------------------------------------------------------
-- Same archival silence can arise under distinct source-generating processes.
------------------------------------------------------------------------

data SilenceCase : Set where
  theatreAdvertSilence : SilenceCase
  coerciveAdvertSilence : SilenceCase

data SilenceReading : Set where
  silentOnVoice : SilenceReading

data ProductionClassCode : Set where
  publicityProduced : ProductionClassCode
  coercivePropertyProduced : ProductionClassCode

observedSilence : SilenceCase → SilenceReading
observedSilence _ = silentOnVoice

productionClassCode : SilenceCase → ProductionClassCode
productionClassCode theatreAdvertSilence = publicityProduced
productionClassCode coerciveAdvertSilence = coercivePropertyProduced

productionClassDiffers :
  productionClassCode theatreAdvertSilence
  ≡ productionClassCode coerciveAdvertSilence → ⊥
productionClassDiffers ()

sameSilenceDifferentProductionContext :
  INF.FactorsThrough observedSilence productionClassCode → ⊥
sameSilenceDifferentProductionContext =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      theatreAdvertSilence
      coerciveAdvertSilence
      refl
      productionClassDiffers)

------------------------------------------------------------------------
-- Attribution / promotion boundaries.
------------------------------------------------------------------------

methodologyAuthority : Methodology.PowersMethodologySourceBoundary
methodologyAuthority = Methodology.canonicalPowersMethodologySourceBoundary

data SourceGenreCreatesHistoricalTruth : Set where

data SourceSilenceTransfersAcrossGenres : Set where

sourceGenreDoesNotCreateHistoricalTruth :
  SourceGenreCreatesHistoricalTruth → ⊥
sourceGenreDoesNotCreateHistoricalTruth ()

sourceSilenceDoesNotTransferAcrossGenres :
  SourceSilenceTransfersAcrossGenres → ⊥
sourceSilenceDoesNotTransferAcrossGenres ()

record PowersArchiveModalityBoundary : Set where
  constructor powers-archive-modality-boundary
  field
    sourceProductionContextIsFirstClass : Bool
    sourceProductionContextIsFirstClassIsTrue :
      sourceProductionContextIsFirstClass ≡ true
    sameSilenceImpliesSameProductionProcess : Bool
    sameSilenceImpliesSameProductionProcessIsFalse :
      sameSilenceImpliesSameProductionProcess ≡ false
    genreCreatesHistoricalTruth : Bool
    genreCreatesHistoricalTruthIsFalse : genreCreatesHistoricalTruth ≡ false
    coerciveDocumentIsNeutralSubjectBiography : Bool
    coerciveDocumentIsNeutralSubjectBiographyIsFalse :
      coerciveDocumentIsNeutralSubjectBiography ≡ false
    silenceTransfersAcrossGenres : Bool
    silenceTransfersAcrossGenresIsFalse : silenceTransfersAcrossGenres ≡ false

canonicalPowersArchiveModalityBoundary : PowersArchiveModalityBoundary
canonicalPowersArchiveModalityBoundary =
  powers-archive-modality-boundary
    true refl
    false refl
    false refl
    false refl
    false refl

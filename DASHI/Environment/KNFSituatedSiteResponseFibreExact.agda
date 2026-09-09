module DASHI.Environment.KNFSituatedSiteResponseFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Environment.KoreanNaturalFarmingExact as KNF
import DASHI.Environment.KNFSoilMicrobePlantFruitResourceLoopExact as Loop
import DASHI.Environment.LESSituatedObservationInteractionExact as Situated

------------------------------------------------------------------------
-- SAME KNF PRACTICE, DIFFERENT SITUATED RESPONSE
--
-- This is a finite formal regression, not an empirical claim about any named
-- farm.  It proves the architecture cannot factor downstream response through
-- KNF practice identity alone when site / season coordinates are erased.
------------------------------------------------------------------------

canonicalSoilIMOApplication : KNF.KNFApplication
canonicalSoilIMOApplication =
  KNF.knf-application
    KNF.canonicalIMO
    KNF.soil
    "fixture: same declared dose"
    "fixture: same nominal timing"
    "site supplied separately by situated observation"

data SituatedKNFResponse : Set where
  responseChanged responseUnchanged : SituatedKNFResponse

record SituatedKNFTrial : Set where
  constructor situated-knf-trial
  field
    application : KNF.KNFApplication
    observation : Situated.SituatedObservation
    microbialResponse : Loop.SoilMicrobialResponse
    nutrientResponse : Loop.SoilNutrientResponse
    response : SituatedKNFResponse

open SituatedKNFTrial public

wetlandWetTrial : SituatedKNFTrial
wetlandWetTrial =
  situated-knf-trial
    canonicalSoilIMOApplication
    Situated.indigenousWetSeasonObservation
    Loop.microbialCommunityChanged
    Loop.nutrientAvailabilityChanged
    responseChanged

uplandWetTrial : SituatedKNFTrial
uplandWetTrial =
  situated-knf-trial
    canonicalSoilIMOApplication
    Situated.uplandWetSeasonObservation
    Loop.microbialCommunityUnchanged
    Loop.nutrientAvailabilityUnchanged
    responseUnchanged

samePractice :
  application wetlandWetTrial ≡ application uplandWetTrial
samePractice = refl

sameAnonymousVisibleReading :
  Situated.anonymousReading (observation wetlandWetTrial) ≡
  Situated.anonymousReading (observation uplandWetTrial)
sameAnonymousVisibleReading = refl

sitesDiffer :
  Situated.site (observation wetlandWetTrial) ≡
  Situated.site (observation uplandWetTrial) → ⊥
sitesDiffer ()

responsesDiffer :
  response wetlandWetTrial ≡ response uplandWetTrial → ⊥
responsesDiffer ()

microbialResponsesDiffer :
  microbialResponse wetlandWetTrial ≡ microbialResponse uplandWetTrial → ⊥
microbialResponsesDiffer ()

nutrientResponsesDiffer :
  nutrientResponse wetlandWetTrial ≡ nutrientResponse uplandWetTrial → ⊥
nutrientResponsesDiffer ()

practiceIdentity : SituatedKNFTrial → KNF.KNFApplication
practiceIdentity = application

practiceIdentityCannotDetermineResponse :
  INF.FactorsThrough practiceIdentity response → ⊥
practiceIdentityCannotDetermineResponse =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      wetlandWetTrial
      uplandWetTrial
      refl
      responsesDiffer)

anonymousReadingCannotDetermineKNFResponse :
  INF.FactorsThrough
    (λ trial → Situated.anonymousReading (observation trial))
    response → ⊥
anonymousReadingCannotDetermineKNFResponse =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      wetlandWetTrial
      uplandWetTrial
      refl
      responsesDiffer)

------------------------------------------------------------------------
-- Measurement packet: practice + situated context + intermediate responses.
------------------------------------------------------------------------

record SituatedKNFMeasurementPacket : Set where
  constructor situated-knf-measurement-packet
  field
    trial : SituatedKNFTrial
    situatedSignature : Situated.SituatedObservationSignature
    signatureMatches :
      situatedSignature ≡
      Situated.situatedObservationSignature (observation trial)
    applicationContextRecorded : Bool
    microbialCoordinateMeasured : Bool
    nutrientCoordinateMeasured : Bool
    downstreamResponseMeasured : Bool

open SituatedKNFMeasurementPacket public

canonicalWetlandMeasurement : SituatedKNFMeasurementPacket
canonicalWetlandMeasurement =
  situated-knf-measurement-packet
    wetlandWetTrial
    (Situated.situatedObservationSignature (observation wetlandWetTrial))
    refl
    true true true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SamePracticeMeansSameOutcomePermission : Set where

data SameVisibleReadingMeansSameSiteResponsePermission : Set where

data FixtureResponseMeansEmpiricalKNFClaimPermission : Set where

data SiteDifferenceExplainsResponsePermission : Set where

samePracticeDoesNotMeanSameOutcome : SamePracticeMeansSameOutcomePermission → ⊥
samePracticeDoesNotMeanSameOutcome ()

sameVisibleReadingDoesNotMeanSameSiteResponse :
  SameVisibleReadingMeansSameSiteResponsePermission → ⊥
sameVisibleReadingDoesNotMeanSameSiteResponse ()

formalFixtureDoesNotCreateEmpiricalKNFClaim :
  FixtureResponseMeansEmpiricalKNFClaimPermission → ⊥
formalFixtureDoesNotCreateEmpiricalKNFClaim ()

siteDifferenceDoesNotByItselfProveCausation :
  SiteDifferenceExplainsResponsePermission → ⊥
siteDifferenceDoesNotByItselfProveCausation ()

record KNFSituatedSiteResponseBoundary : Set where
  constructor knf-situated-site-response-boundary
  field
    samePracticeMayOccupyDifferentSiteFibres : Bool
    sameAnonymousReadingMayHideDifferentSite : Bool
    practiceIdentityAloneMayBeInsufficientForResponse : Bool
    situatedMeasurementRetainsContext : Bool
    formalFixtureIsEmpiricalGeneralisation : Bool
    siteDifferenceAloneEstablishesCausalMechanism : Bool

canonicalKNFSituatedSiteResponseBoundary : KNFSituatedSiteResponseBoundary
canonicalKNFSituatedSiteResponseBoundary =
  knf-situated-site-response-boundary
    true true true true false false

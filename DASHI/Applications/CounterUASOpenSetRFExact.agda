module DASHI.Applications.CounterUASOpenSetRFExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- OPEN-SET RF DETECTION BOUNDARY
--
-- Core distinction:
--
--   spectrum activity
--     != known-library match
--     != emitter identity
--     != UAS identity
--     != threat
--     != mitigation authority
--
-- This owner formalises only defensive observation/classification semantics.
-- It contains no waveform, power, targeting, or disruption recipe.
------------------------------------------------------------------------

data RFDetectionState : Set where
  noRFActivity : RFDetectionState
  knownLibraryMatch : RFDetectionState
  unknownRFActivity : RFDetectionState
  unresolvedRFActivity : RFDetectionState

noCatalogMatchDoesNotImplyNoDetection : Bool
noCatalogMatchDoesNotImplyNoDetection = true

rfActivityDoesNotCreateEmitterIdentity : Bool
rfActivityDoesNotCreateEmitterIdentity = true

openSetDetectionDoesNotCreateKnownClass : Bool
openSetDetectionDoesNotCreateKnownClass = true

generatedSignatureDoesNotCreateIdentityAuthority : Bool
generatedSignatureDoesNotCreateIdentityAuthority = true

------------------------------------------------------------------------
-- I. Catalog lookup is inadequate for the query "is RF activity present?"
--
-- quietSpectrum and novelEmission have the same catalog result (no match),
-- but different activity answers.  Therefore detection does not factor through
-- catalog membership alone.
------------------------------------------------------------------------

data RFWorld : Set where
  quietSpectrum : RFWorld
  cataloguedEmission : RFWorld
  novelEmission : RFWorld

data CatalogSurface : Set where
  noCatalogMatch : CatalogSurface
  catalogMatch : CatalogSurface

data RFQuery : Set where
  activityQuery : RFQuery
  knownMatchQuery : RFQuery

data RFAnswer : Set where
  activityAbsent : RFAnswer
  activityPresent : RFAnswer
  knownMatchAbsent : RFAnswer
  knownMatchPresent : RFAnswer

catalogOnlyProjection : RFWorld → CatalogSurface
catalogOnlyProjection quietSpectrum = noCatalogMatch
catalogOnlyProjection cataloguedEmission = catalogMatch
catalogOnlyProjection novelEmission = noCatalogMatch

rfAnswer : RFQuery → RFWorld → RFAnswer
rfAnswer activityQuery quietSpectrum = activityAbsent
rfAnswer activityQuery cataloguedEmission = activityPresent
rfAnswer activityQuery novelEmission = activityPresent
rfAnswer knownMatchQuery quietSpectrum = knownMatchAbsent
rfAnswer knownMatchQuery cataloguedEmission = knownMatchPresent
rfAnswer knownMatchQuery novelEmission = knownMatchAbsent

rfSemantics : Adequacy.QuerySemantics RFWorld RFQuery RFAnswer
rfSemantics = Adequacy.querySemantics rfAnswer

catalogOnlyDetectionAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    catalogOnlyProjection
    rfSemantics
    activityQuery
catalogOnlyDetectionAdequacyDefect =
  Adequacy.queryAdequacyDefect
    quietSpectrum
    novelEmission
    refl
    (λ ())

catalogOnlyCannotDetermineRFActivity :
  Adequacy.AdequateFor catalogOnlyProjection rfSemantics activityQuery → ⊥
catalogOnlyCannotDetermineRFActivity =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    catalogOnlyDetectionAdequacyDefect

activityProjection : RFWorld → Bool
activityProjection quietSpectrum = false
activityProjection cataloguedEmission = true
activityProjection novelEmission = true

catalogAndActivityProjection : RFWorld → CatalogSurface × Bool
catalogAndActivityProjection =
  Observer.pairObserver catalogOnlyProjection activityProjection

joinedActivityAnswer : CatalogSurface × Bool → RFAnswer
joinedActivityAnswer (noCatalogMatch , false) = activityAbsent
joinedActivityAnswer (noCatalogMatch , true) = activityPresent
joinedActivityAnswer (catalogMatch , false) = activityAbsent
joinedActivityAnswer (catalogMatch , true) = activityPresent

catalogAndActivityDetermineRFActivity :
  Adequacy.AdequateFor catalogAndActivityProjection rfSemantics activityQuery
catalogAndActivityDetermineRFActivity =
  Adequacy.factorsForQuery
    joinedActivityAnswer
    (λ { quietSpectrum → refl
       ; cataloguedEmission → refl
       ; novelEmission → refl
       })

------------------------------------------------------------------------
-- II. Anomaly/open-set detection is inadequate for identity.
--
-- Two worlds can present the same unknown/anomalous RF surface while one is
-- UAS-origin and the other is not.  Thus surfacing an unknown is an observation
-- achievement, not an identity theorem.
------------------------------------------------------------------------

data OpenSetWorld : Set where
  unknownUASEmission : OpenSetWorld
  unknownNonUASEmission : OpenSetWorld

data AnomalySurface : Set where
  sameUnknownRFAnomaly : AnomalySurface

data OpenSetQuery : Set where
  anomalyQuery : OpenSetQuery
  identityQuery : OpenSetQuery

data OpenSetAnswer : Set where
  anomalyDetected : OpenSetAnswer
  uasOrigin : OpenSetAnswer
  nonUASOrigin : OpenSetAnswer

anomalyOnlyProjection : OpenSetWorld → AnomalySurface
anomalyOnlyProjection world = sameUnknownRFAnomaly

openSetAnswer : OpenSetQuery → OpenSetWorld → OpenSetAnswer
openSetAnswer anomalyQuery world = anomalyDetected
openSetAnswer identityQuery unknownUASEmission = uasOrigin
openSetAnswer identityQuery unknownNonUASEmission = nonUASOrigin

openSetSemantics :
  Adequacy.QuerySemantics OpenSetWorld OpenSetQuery OpenSetAnswer
openSetSemantics = Adequacy.querySemantics openSetAnswer

anomalyOnlyIdentityAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    anomalyOnlyProjection
    openSetSemantics
    identityQuery
anomalyOnlyIdentityAdequacyDefect =
  Adequacy.queryAdequacyDefect
    unknownUASEmission
    unknownNonUASEmission
    refl
    (λ ())

anomalyOnlyCannotDetermineIdentity :
  Adequacy.AdequateFor anomalyOnlyProjection openSetSemantics identityQuery → ⊥
anomalyOnlyCannotDetermineIdentity =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    anomalyOnlyIdentityAdequacyDefect

------------------------------------------------------------------------
-- III. Generated signatures are evidence references, not authority tokens.
------------------------------------------------------------------------

record GeneratedSignatureReference : Set where
  constructor generatedSignatureReference
  field
    signatureLabel : String
    priorEncounterReference : String
    sourceProvenanceRetained : Bool
    sourceProvenanceRetainedIsTrue : sourceProvenanceRetained ≡ true
    createsEmitterIdentityAuthority : Bool
    createsEmitterIdentityAuthorityIsFalse :
      createsEmitterIdentityAuthority ≡ false
    createsThreatAuthority : Bool
    createsThreatAuthorityIsFalse : createsThreatAuthority ≡ false

open GeneratedSignatureReference public

mkGeneratedSignatureReference : String → String → GeneratedSignatureReference
mkGeneratedSignatureReference label encounter =
  generatedSignatureReference
    label
    encounter
    true refl
    false refl
    false refl

record OpenSetRFBoundary : Set where
  constructor openSetRFBoundary
  field
    catalogMissEqualsNoDetection : Bool
    catalogMissEqualsNoDetectionIsFalse : catalogMissEqualsNoDetection ≡ false
    anomalyEqualsKnownClass : Bool
    anomalyEqualsKnownClassIsFalse : anomalyEqualsKnownClass ≡ false
    generatedSignatureEqualsIdentityAuthority : Bool
    generatedSignatureEqualsIdentityAuthorityIsFalse :
      generatedSignatureEqualsIdentityAuthority ≡ false
    generatedSignatureEqualsThreatAuthority : Bool
    generatedSignatureEqualsThreatAuthorityIsFalse :
      generatedSignatureEqualsThreatAuthority ≡ false

canonicalOpenSetRFBoundary : OpenSetRFBoundary
canonicalOpenSetRFBoundary =
  openSetRFBoundary false refl false refl false refl false refl

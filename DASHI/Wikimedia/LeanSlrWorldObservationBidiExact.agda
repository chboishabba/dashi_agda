module DASHI.Wikimedia.LeanSlrWorldObservationBidiExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.AristotleLeanMachineAttributionExact as Attribution
import DASHI.Wikimedia.SLRWikimediaHandoffABIExact as SlrABI

------------------------------------------------------------------------
-- GOLDEN WORLD-OBSERVATION ABI
--
-- Agda owns the semantics.  JMD Lean and SLR may use different getter
-- implementations, but both must project into the same revision/digest-bound
-- observation carrier before parity is assessed.
------------------------------------------------------------------------

data RetrievalStatus : Set where
  retrievalSucceeded : RetrievalStatus
  retrievalNoMatch : RetrievalStatus
  retrievalBlocked : RetrievalStatus
  retrievalFailed : RetrievalStatus

data FreshnessStatus : Set where
  currentFreshness : FreshnessStatus
  staleFreshness : FreshnessStatus
  unknownFreshness : FreshnessStatus

data ProvenanceClass : Set where
  statedInProvenance : ProvenanceClass
  referenceURLProvenance : ProvenanceClass
  importedFromProvenance : ProvenanceClass
  providerRevisionProvenance : ProvenanceClass
  unknownProvenance : ProvenanceClass

record WorldObservation : Set where
  constructor world-observation
  field
    requestReference : String
    objectReference : String
    relationReference : String
    sourceReference : String
    sourceRevisionReference : String
    contentDigestReference : String
    observedValueReference : String
    retrievalStatus : RetrievalStatus
    freshnessStatus : FreshnessStatus
    provenanceClass : ProvenanceClass
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open WorldObservation public

mkWorldObservation :
  String → String → String → String → String → String → String →
  RetrievalStatus → FreshnessStatus → ProvenanceClass →
  WorldObservation
mkWorldObservation request object relation source revision digest value retrieval freshness provenance =
  world-observation
    request object relation source revision digest value retrieval freshness provenance
    true refl false refl false refl

record LeanGetterObservation : Set where
  constructor lean-getter-observation
  field
    leanObservation : WorldObservation
    leanGetterBackendReference : String
    getterUsesGoldenObservationABI : Bool
    getterUsesGoldenObservationABIIsTrue : getterUsesGoldenObservationABI ≡ true
    getterCreatesSemanticAuthority : Bool
    getterCreatesSemanticAuthorityIsFalse : getterCreatesSemanticAuthority ≡ false
    getterCreatesClaimTruth : Bool
    getterCreatesClaimTruthIsFalse : getterCreatesClaimTruth ≡ false

open LeanGetterObservation public

mkLeanGetterObservation : WorldObservation → String → LeanGetterObservation
mkLeanGetterObservation observation backend =
  lean-getter-observation observation backend true refl false refl false refl

record SlrGetterObservation : Set where
  constructor slr-getter-observation
  field
    slrObservation : WorldObservation
    slrGetterBackendReference : String
    slrGetterUsesGoldenObservationABI : Bool
    slrGetterUsesGoldenObservationABIIsTrue : slrGetterUsesGoldenObservationABI ≡ true
    slrGetterCreatesSemanticAuthority : Bool
    slrGetterCreatesSemanticAuthorityIsFalse : slrGetterCreatesSemanticAuthority ≡ false
    slrGetterCreatesClaimTruth : Bool
    slrGetterCreatesClaimTruthIsFalse : slrGetterCreatesClaimTruth ≡ false

open SlrGetterObservation public

mkSlrGetterObservation : WorldObservation → String → SlrGetterObservation
mkSlrGetterObservation observation backend =
  slr-getter-observation observation backend true refl false refl false refl

normalizeLeanGetter : LeanGetterObservation → WorldObservation
normalizeLeanGetter = leanObservation

normalizeSlrGetter : SlrGetterObservation → WorldObservation
normalizeSlrGetter = slrObservation

data GetterMismatchKind : Set where
  valueMismatch : GetterMismatchKind
  revisionMismatch : GetterMismatchKind
  missingClaimMismatch : GetterMismatchKind
  typeMismatch : GetterMismatchKind
  provenanceMismatch : GetterMismatchKind
  parserMismatch : GetterMismatchKind

record GetterParityResidual : Set where
  constructor getterParityResidual
  field
    parityResidualReference : String
    leanGetter : LeanGetterObservation
    slrGetter : SlrGetterObservation
    mismatchKind : GetterMismatchKind
    disagreementChoosesWorldTruth : Bool
    disagreementCreatesAuthority : Bool

open GetterParityResidual public

data GetterBackendDeterminesObservationSemantics : Set where
data GetterDisagreementDeterminesWorldTruth : Set where

data ImportedFromMeansIndependentSource : Set where

getterBackendDoesNotDetermineObservationSemantics :
  GetterBackendDeterminesObservationSemantics → ⊥
getterBackendDoesNotDetermineObservationSemantics ()

getterDisagreementDoesNotDetermineWorldTruth :
  GetterDisagreementDeterminesWorldTruth → ⊥
getterDisagreementDoesNotDetermineWorldTruth ()

importedFromDoesNotMeanIndependentSource :
  ImportedFromMeansIndependentSource → ⊥
importedFromDoesNotMeanIndependentSource ()

------------------------------------------------------------------------
-- Source / downstream ownership pins.
------------------------------------------------------------------------

jmdSourceAttribution : Attribution.AristotleLeanMachineAttributionReceipt
jmdSourceAttribution = Attribution.jmdLeanArchiveAttributionReceipt

slrObservationConsumerBoundary : String
slrObservationConsumerBoundary = SlrABI.slrSourceHandoffImplementationReference

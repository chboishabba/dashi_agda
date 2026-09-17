module DASHI.Wikimedia.MaboWorldObservationInteropValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Wikimedia.MaboWorldObservationInteropExact
import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact as Observation

maboObjectPinned :
  Observation.objectReference maboP710Observation ≡ "Q1501525"
maboObjectPinned = refl

maboPropertyPinned :
  Observation.relationReference maboP710Observation ≡ "P710"
maboPropertyPinned = refl

maboValuePinned :
  Observation.observedValueReference maboP710Observation ≡ "Q975866"
maboValuePinned = refl

maboRevisionPinned :
  Observation.sourceRevisionReference maboP710Observation
  ≡ "wikidata:Q1501525:oldid:2333409615"
maboRevisionPinned = refl

maboDigestPinned :
  Observation.contentDigestReference maboP710Observation
  ≡ "sha256:43681681a832e9d0edf09f745c7d3e71fd4cdb9fd23d4670f25e5b94827b5eba"
maboDigestPinned = refl

slrNativeRuntimeObserved : maboSlrRuntimeObservationObserved ≡ true
slrNativeRuntimeObserved = refl

interopRuntimeStillUnobserved : maboInteropRuntimeObservationObserved ≡ false
interopRuntimeStillUnobserved = refl

crossRuntimeParityStillUnobserved : maboCrossRuntimeParityObserved ≡ false
crossRuntimeParityStillUnobserved = refl

nativeAndInteropNormalizeToSameMaboObservation :
  Observation.normalizeSlrGetter maboSlrGetterFixture
  ≡ Observation.normalizeLeanGetter maboInteropGetterFixture
nativeAndInteropNormalizeToSameMaboObservation = refl

natClimateObjectPinned :
  Observation.objectReference natClimateObservation ≡ "Q10884"
natClimateObjectPinned = refl

natClimateRevisionPinned :
  Observation.sourceRevisionReference natClimateObservation
  ≡ "provided_snapshot_2026-04-01"
natClimateRevisionPinned = refl

maboAdapterPreservesTriggeringResidual :
  triggeringResidualReference maboP710CandidateProjection
  ≡ "residual:mabo:participant-identity"
maboAdapterPreservesTriggeringResidual = refl

maboAdapterPreservesSourceRevision :
  candidateSourceRevisionReference maboP710CandidateProjection
  ≡ "wikidata:Q1501525:oldid:2333409615"
maboAdapterPreservesSourceRevision = refl

maboAdapterPreservesContentDigest :
  candidateContentDigestReference maboP710CandidateProjection
  ≡ "sha256:43681681a832e9d0edf09f745c7d3e71fd4cdb9fd23d4670f25e5b94827b5eba"
maboAdapterPreservesContentDigest = refl

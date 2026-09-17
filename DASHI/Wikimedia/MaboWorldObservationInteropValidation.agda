module DASHI.Wikimedia.MaboWorldObservationInteropValidation where

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

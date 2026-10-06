module DASHI.Governance.OccupyArchivalObservationModelRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyArchivalObservationModelExact as Obs

codingFidelityIsSeparate :
  Obs.codingFidelityIsDocumentaryCompleteness Obs.canonicalObservationBoundary ≡ false
codingFidelityIsSeparate = refl

documentaryCompletenessNotAssumed :
  Obs.documentaryCompletenessAssumed Obs.canonicalObservationBoundary ≡ false
documentaryCompletenessNotAssumed = refl

documentarySoundnessNotAssumed :
  Obs.documentarySoundnessAssumed Obs.canonicalObservationBoundary ≡ false
documentarySoundnessNotAssumed = refl

codedEdgeDoesNotByItselfProveEventTruth :
  Obs.codedEdgeAloneProvesEventInteraction Obs.canonicalObservationBoundary ≡ false
codedEdgeDoesNotByItselfProveEventTruth = refl

conditionalTransportRequiresBothLayers :
  Obs.transportToEventRequiresCodingAndDocumentaryWitnesses Obs.canonicalObservationBoundary ≡ true
conditionalTransportRequiresBothLayers = refl

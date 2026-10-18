module DASHI.Law.SensibLawUnifiedWorkbenchPersistedProofGraphRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawUnifiedWorkbenchPersistedProofGraphExact as P

absentStillUnavailable :
  P.absentGraphProjectsUnavailable
    P.canonicalPersistedProofGraphBoundary
  ≡ true
absentStillUnavailable = refl

presentStillAvailable :
  P.presentGraphProjectsAvailable
    P.canonicalPersistedProofGraphBoundary
  ≡ true
presentStillAvailable = refl

uiStillCannotInferGraph :
  P.uiMayInferMissingGraph
    P.canonicalPersistedProofGraphBoundary
  ≡ false
uiStillCannotInferGraph = refl

rendererStillCannotCreateGraph :
  P.rendererMayCreateGraph
    P.canonicalPersistedProofGraphBoundary
  ≡ false
rendererStillCannotCreateGraph = refl

graphPresenceStillDoesNotCreateAuthority :
  P.graphPresenceCreatesAuthority
    P.canonicalPersistedProofGraphBoundary
  ≡ false
graphPresenceStillDoesNotCreateAuthority = refl

graphPresenceStillDoesNotCreateTruth :
  P.graphPresenceCreatesTruth
    P.canonicalPersistedProofGraphBoundary
  ≡ false
graphPresenceStillDoesNotCreateTruth = refl

graphPresenceStillDoesNotPayResidual :
  P.graphPresencePaysResidual
    P.canonicalPersistedProofGraphBoundary
  ≡ false
graphPresenceStillDoesNotPayResidual = refl

keywordInferenceStillImpossible :
  P.UiInfersProofGraphFromKeywords → ⊥
keywordInferenceStillImpossible =
  P.uiCannotInferProofGraph

module DASHI.Law.SensibLawUnifiedWorkbenchProjectionRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawUnifiedWorkbenchProjectionExact as W

sharedStateStillExplicit :
  W.journalTimelineHandoffProofResearchShareState
    W.canonicalUnifiedWorkbenchBoundary
  ≡ true
sharedStateStillExplicit = refl

unavailableStillExplicit :
  W.unavailableProjectionRemainsExplicit
    W.canonicalUnifiedWorkbenchBoundary
  ≡ true
unavailableStillExplicit = refl

stageChangeStillDoesNotCreateAuthority :
  W.stageChangeCreatesAuthority
    W.canonicalUnifiedWorkbenchBoundary
  ≡ false
stageChangeStillDoesNotCreateAuthority = refl

stageChangeStillDoesNotCreateTruth :
  W.stageChangeCreatesTruth
    W.canonicalUnifiedWorkbenchBoundary
  ≡ false
stageChangeStillDoesNotCreateTruth = refl

stageChangeStillDoesNotPayResidual :
  W.stageChangePaysResidual
    W.canonicalUnifiedWorkbenchBoundary
  ≡ false
stageChangeStillDoesNotPayResidual = refl

projectionStillDoesNotCreateSecondWorld :
  W.projectionCreatesSecondWorld
    W.canonicalUnifiedWorkbenchBoundary
  ≡ false
projectionStillDoesNotCreateSecondWorld = refl

unavailableStillDoesNotMeanFalse :
  W.UnavailableMeansFalse → ⊥
unavailableStillDoesNotMeanFalse =
  W.unavailableDoesNotMeanFalse

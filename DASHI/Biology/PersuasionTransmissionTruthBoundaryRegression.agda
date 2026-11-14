module DASHI.Biology.PersuasionTransmissionTruthBoundaryRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.PersuasionTransmissionTruthBoundaryExact as X

persuasionTransmissionDistinct :
  X.persuasionCollapsedWithTransmission X.canonicalTruthTransmissionBoundary ≡ false
persuasionTransmissionDistinct = refl

positiveEmotionNotTruthAuthority :
  X.positiveEmotionCreatesTruthAuthority X.canonicalTruthTransmissionBoundary ≡ false
positiveEmotionNotTruthAuthority = refl

truthIntentRepresented :
  X.truthIntentAdvantageRepresented X.canonicalTruthTransmissionBoundary ≡ true
truthIntentRepresented = refl

realWorldUniversalizationBlocked :
  X.controlledExperimentUniversalizesToPlatforms X.canonicalTruthTransmissionBoundary ≡ false
realWorldUniversalizationBlocked = refl

fayOutcomeSourceBound :
  X.AdmittedPersuasionSource X.fay2026ControlledExperimentOutcome X.fay2026Source
fayOutcomeSourceBound = X.fay2026PaysControlledExperimentOutcome

unadmittedSourceCannotPayOutcome :
  {source : Source.AttributedSource} →
  X.AdmittedPersuasionSource X.unadmittedPersuasionOutcome source → ⊥
unadmittedSourceCannotPayOutcome ()

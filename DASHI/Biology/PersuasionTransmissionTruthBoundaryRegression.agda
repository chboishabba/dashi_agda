module DASHI.Biology.PersuasionTransmissionTruthBoundaryRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

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

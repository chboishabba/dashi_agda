module DASHI.Law.SensibLawUnifiedWorkbenchInteractionIRBridgeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawUnifiedWorkbenchInteractionIRBridgeExact as I

interfaceIrStillOwnsControls :
  I.interfaceIrOwnsDeclarativeControls
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ true
interfaceIrStillOwnsControls = refl

interactionIrStillOwnsIntent :
  I.interactionIrOwnsIntentVocabulary
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ true
interactionIrStillOwnsIntent = refl

shellGpuStillShareCommandLanguage :
  I.shellAndGpuRefineSameCommandLanguage
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ true
shellGpuStillShareCommandLanguage = refl

physicalGestureStillNotCanonical :
  I.physicalGestureIsCanonicalIntent
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ false
physicalGestureStillNotCanonical = refl

cssSelectorStillNotCanonical :
  I.cssSelectorIsCanonicalTarget
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ false
cssSelectorStillNotCanonical = refl

interactionStillDoesNotCreateAuthority :
  I.interactionCreatesSemanticAuthority
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ false
interactionStillDoesNotCreateAuthority = refl

interactionStillDoesNotCreateTruth :
  I.interactionCreatesClaimTruth
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ false
interactionStillDoesNotCreateTruth = refl

interactionStillDoesNotPayResidual :
  I.interactionPaysResidual
    I.canonicalUnifiedWorkbenchInteractionIRBoundary
  ≡ false
interactionStillDoesNotPayResidual = refl

hiddenVisualStillNotAbsent :
  I.HiddenVisualObjectAbsentFromWorld → ⊥
hiddenVisualStillNotAbsent =
  I.hiddenVisualObjectStillExistsSemantically

module DASHI.Biology.TranslationInvariantCompletionAccessibilityNonfactorabilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

------------------------------------------------------------------------
-- TRANSLATION-INVARIANT COMPLETION READOUT != EMBODIED ACCESSIBILITY
--
-- The completed T^2_3 carrier fixes its distinguished completion channel under
-- both ordinary translations.  This module combines that exact invariance with
-- a finite non-factorability witness: an invariant completion readout is too
-- coarse to reconstruct embodied accessibility.
--
-- Source context:
-- Audrey Terras, "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
------------------------------------------------------------------------

completionReadout : ∀ {State : Set} → Torus.Field State → State
completionReadout field = field Torus.completionChannel

completionReadoutFirstInvariant : ∀ {State : Set} (field : Torus.Field State) →
  completionReadout (Torus.pullbackFirst field) ≡ completionReadout field
completionReadoutFirstInvariant field = refl

completionReadoutSecondInvariant : ∀ {State : Set} (field : Torus.Field State) →
  completionReadout (Torus.pullbackSecond field) ≡ completionReadout field
completionReadoutSecondInvariant field = refl

data CompletionEmbodiedState : Set where
  regulatedCompletion mobilisedCompletion : CompletionEmbodiedState

data CompletionSurface : Set where
  sameCompletionReadout : CompletionSurface

data AccessibilityState : Set where
  broadAccess contractedAccess : AccessibilityState

completionProjection : CompletionEmbodiedState → CompletionSurface
completionProjection regulatedCompletion = sameCompletionReadout
completionProjection mobilisedCompletion = sameCompletionReadout

embodiedAccessibility : CompletionEmbodiedState → AccessibilityState
embodiedAccessibility regulatedCompletion = broadAccess
embodiedAccessibility mobilisedCompletion = contractedAccess

completionSame :
  completionProjection regulatedCompletion
  ≡ completionProjection mobilisedCompletion
completionSame = refl

accessibilityDiffers :
  embodiedAccessibility regulatedCompletion
  ≡ embodiedAccessibility mobilisedCompletion → ⊥
accessibilityDiffers ()

completionAccessibilityNonfactorability :
  NF.NonFactorabilityWitness completionProjection embodiedAccessibility
completionAccessibilityNonfactorability =
  NF.nonFactorabilityWitness
    regulatedCompletion
    mobilisedCompletion
    refl
    accessibilityDiffers

completionSurfaceCannotDecodeAccessibility :
  NF.FactorsThrough completionProjection embodiedAccessibility → ⊥
completionSurfaceCannotDecodeAccessibility =
  NF.witnessRulesOutEveryFlatFactorisation
    completionAccessibilityNonfactorability

record CompletionAccessibilityBoundary : Set where
  constructor completionAccessibilityBoundary
  field
    completionTranslationInvariant : Bool
    completionReadoutDeterminesEmbodiedAccessibility : Bool
    completionChannelIsGlobalWorkspace : Bool
    completionChannelIsConsciousness : Bool

canonicalCompletionAccessibilityBoundary : CompletionAccessibilityBoundary
canonicalCompletionAccessibilityBoundary =
  completionAccessibilityBoundary true false false false

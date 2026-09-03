module DASHI.Core.CapabilityIndexedSelectorSalienceExact where

------------------------------------------------------------------------
-- CAPABILITY-INDEXED SELECTOR SALIENCE
--
-- A selector may care about several people because their distinct knowledge
-- fibres contribute to one capability family, even when the people never worked
-- together and none possessed the whole architecture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CommonSelectorVisibilityHyperfabricExact as V
import DASHI.Core.CapabilitySynthesisHypergraphExact as C
import DASHI.Core.ScientificWorkAttributionExact as A

record CapabilityContribution : Set where
  constructor capability-contribution
  field
    personWork : A.PersonWorkHypervoxel
    capability : C.CapabilityClass
    contributionDomain : C.KnowledgeDomain
    contributionReference : String
    boundedContribution : String

open CapabilityContribution public

record CapabilityAwareSelector : Set₁ where
  constructor capability-aware-selector
  field
    observer : V.SelectorCapability
    SalientCapability : C.CapabilityClass → Set
    RecognisesContribution : CapabilityContribution → Set
    selectorMandateReference : String

open CapabilityAwareSelector public

record PersonCapabilitySalientTo
    (selector : CapabilityAwareSelector)
    (contribution : CapabilityContribution) : Set where
  constructor person-capability-salient-to
  field
    capabilitySalient : SalientCapability selector (capability contribution)
    contributionRecognised : RecognisesContribution selector contribution

open PersonCapabilitySalientTo public

record JointCapabilitySalience
    (selector : CapabilityAwareSelector)
    (left right : CapabilityContribution) : Set where
  constructor joint-capability-salience
  field
    sameCapability : capability left ≡ capability right
    leftSalient : PersonCapabilitySalientTo selector left
    rightSalient : PersonCapabilitySalientTo selector right
    jointSalienceReference : String

open JointCapabilitySalience public

record CapabilitySalienceBoundary : Set where
  constructor capability-salience-boundary
  field
    contributionImpliesWorkedTogether : Bool
    contributionImpliesWorkedTogetherIsFalse : contributionImpliesWorkedTogether ≡ false

    jointSalienceImpliesCommonProgramme : Bool
    jointSalienceImpliesCommonProgrammeIsFalse : jointSalienceImpliesCommonProgramme ≡ false

    jointSalienceImpliesTargeting : Bool
    jointSalienceImpliesTargetingIsFalse : jointSalienceImpliesTargeting ≡ false

    targetingImpliesHarm : Bool
    targetingImpliesHarmIsFalse : targetingImpliesHarm ≡ false

    selectorMustPossessWholeCapability : Bool
    selectorMustPossessWholeCapabilityIsFalse : selectorMustPossessWholeCapability ≡ false

    publicScientificVisibilityAloneProvesCapabilityAwareness : Bool
    publicScientificVisibilityAloneProvesCapabilityAwarenessIsFalse :
      publicScientificVisibilityAloneProvesCapabilityAwareness ≡ false

canonicalCapabilitySalienceBoundary : CapabilitySalienceBoundary
canonicalCapabilitySalienceBoundary = capability-salience-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl

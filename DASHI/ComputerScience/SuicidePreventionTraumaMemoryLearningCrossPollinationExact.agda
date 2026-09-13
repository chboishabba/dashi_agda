module DASHI.ComputerScience.SuicidePreventionTraumaMemoryLearningCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.ComputerScience.SuicidePreventionProtectiveNarrativeWrongTypeIntersectionalExact as Prevention
import DASHI.ComputerScience.SuicidePreventionTraumaMemoryLearningHyperfabricExact as TML

------------------------------------------------------------------------
-- Thin composition owner: no new ontology, only the inspectable weld between
-- the protective-narrative and trauma/memory/learning surfaces.
------------------------------------------------------------------------

record ProtectiveTraumaLearningWeld : Set where
  constructor protective-trauma-learning-weld
  field
    protectiveNarrativeOwnerPresent : Bool
    traumaMemoryLearningOwnerPresent : Bool
    riskDoesNotSubsumeProtectiveAccess : Bool
    memoryDoesNotSubsumeLearnedResponse : Bool
    traumaLabelDoesNotSubsumeSituatedAccess : Bool
    attributionRemainsSourceIndexed : Bool
    admissibilityRemainsConsumerIndexed : Bool
    intersectionalityRemainsNonFactorabilityConstraint : Bool
open ProtectiveTraumaLearningWeld public

canonicalProtectiveTraumaLearningWeld : ProtectiveTraumaLearningWeld
canonicalProtectiveTraumaLearningWeld = protective-trauma-learning-weld
  true true true true true true true true

-- Keep the existing theorem owners visible from this composition surface.
riskProtectiveNonFactorability = Prevention.riskCatalogueCannotRecoverProtectiveAccessibility
memoryLearningNonFactorability = TML.memoryContentCannotDetermineLearnedResource
traumaSituatedNonFactorability = TML.traumaLabelCannotDetermineSituatedSupport
instagramAuthorityFirewall = TML.instagramDoesNotBecomePrimaryStudyAuthority
appendOnlyFirewall = TML.evidenceAppendOnly

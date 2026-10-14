module DASHI.Biology.PersuasionTransmissionTruthBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.AutismVaccinePersuasionMediaExtensionExact as Media

fay2026Source : Source.AttributedSource
fay2026Source =
  Source.mkDOISource
    "Nicolas Fay; Keith J Ransom; Bradley Walker; Piers D L Howe; Andrew Perfors; Yoshihisa Kashima"
    "Truth over falsehood: Experimental evidence on what persuades and spreads"
    "Journal of Personality and Social Psychology 130(4):684-700"
    "2026"
    "10.1037/pspa0000467"
    "https://doi.org/10.1037/pspa0000467"
    Source.academicArticleSource
    "Four controlled experiments (combined N=4,607) found messages created with truthful intent were more persuasive and more likely to be shared than messages created to be false. Perceived truth was the main driver of persuasion, while transmission was primarily associated with positive emotion and social engagement. Generalization beyond the controlled setting remains bounded."
    Source.publicAttribution

------------------------------------------------------------------------
-- ATTRIBUTION / OUTCOME BINDING
--
-- The source record is provenance.  An outcome receipt additionally needs a
-- family-specific admission witness.  This witness does not import truth or
-- causal authority; it only prevents unrelated/design-only sources from being
-- substituted for the completed controlled-experiment result family.
------------------------------------------------------------------------

data PersuasionOutcomeFamily : Set where
  fay2026ControlledExperimentOutcome : PersuasionOutcomeFamily
  unadmittedPersuasionOutcome : PersuasionOutcomeFamily

data AdmittedPersuasionSource :
  PersuasionOutcomeFamily → Source.AttributedSource → Set where
  fay2026PaysControlledExperimentOutcome :
    AdmittedPersuasionSource fay2026ControlledExperimentOutcome fay2026Source

record PersuasionTransmissionReceipt : Set where
  constructor persuasion-transmission-receipt
  field
    source : Source.AttributedSource
    sourceAdmission :
      AdmittedPersuasionSource fay2026ControlledExperimentOutcome source
    combinedSampleReference : String
    truthfulIntentPersuasionAdvantage : Bool
    truthfulIntentPersuasionAdvantageIsTrue : truthfulIntentPersuasionAdvantage ≡ true
    truthfulIntentSharingAdvantage : Bool
    truthfulIntentSharingAdvantageIsTrue : truthfulIntentSharingAdvantage ≡ true
    perceivedTruthPrimaryPersuasionDriver : Bool
    perceivedTruthPrimaryPersuasionDriverIsTrue : perceivedTruthPrimaryPersuasionDriver ≡ true
    positiveEmotionSocialEngagementTransmissionDriver : Bool
    positiveEmotionSocialEngagementTransmissionDriverIsTrue :
      positiveEmotionSocialEngagementTransmissionDriver ≡ true
    persuasionEqualsTransmission : Bool
    persuasionEqualsTransmissionIsFalse : persuasionEqualsTransmission ≡ false
    positiveEmotionDeterminesPropositionTruth : Bool
    positiveEmotionDeterminesPropositionTruthIsFalse :
      positiveEmotionDeterminesPropositionTruth ≡ false
    uncontrolledPlatformGeneralizationPaid : Bool
    uncontrolledPlatformGeneralizationPaidIsFalse :
      uncontrolledPlatformGeneralizationPaid ≡ false

canonicalPersuasionTransmissionReceipt : PersuasionTransmissionReceipt
canonicalPersuasionTransmissionReceipt =
  persuasion-transmission-receipt
    fay2026Source fay2026PaysControlledExperimentOutcome
    "four experiments; combined N=4,607"
    true refl true refl true refl true refl false refl false refl false refl

data PositiveEmotionCreatesTruthPermission : Set where
data PersuasionEqualsTransmissionPermission : Set where

positiveEmotionDoesNotCreateTruth : PositiveEmotionCreatesTruthPermission → ⊥
positiveEmotionDoesNotCreateTruth ()

persuasionDoesNotCollapseToTransmission : PersuasionEqualsTransmissionPermission → ⊥
persuasionDoesNotCollapseToTransmission ()

record TruthTransmissionBoundary : Set where
  constructor truth-transmission-boundary
  field
    truthIntentAdvantageRepresented : Bool
    persuasionCollapsedWithTransmission : Bool
    positiveEmotionCreatesTruthAuthority : Bool
    controlledExperimentUniversalizesToPlatforms : Bool
    existingPropagationNonautomaticityRetained : Bool

open TruthTransmissionBoundary public

canonicalTruthTransmissionBoundary : TruthTransmissionBoundary
canonicalTruthTransmissionBoundary =
  truth-transmission-boundary true false false false true

existingExposureBeliefBoundary : Media.automatic Media.exposureToBelief ≡ false
existingExposureBeliefBoundary = refl

existingBeliefIntentBoundary : Media.automatic Media.beliefToIntent ≡ false
existingBeliefIntentBoundary = refl

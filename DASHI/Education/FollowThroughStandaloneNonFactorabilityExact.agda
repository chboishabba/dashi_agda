module DASHI.Education.FollowThroughStandaloneNonFactorabilityExact where

-- Synthetic educational-outcome / learner-voice counterexample.
-- Not historical Project Follow Through data.
-- Formalisation: Johl Brown (research direction), OpenAI ChatGPT
-- (AI-assisted implementation). Original studies retain original credit.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as INF

data InstructionHistory : Set where
  masteryWithVoice : InstructionHistory
  masteryWithoutVoice : InstructionHistory

data AcademicSurface : Set where sameMastery : AcademicSurface

data VoiceSurface : Set where
  voice : VoiceSurface
  noVoice : VoiceSurface

academicProjection : InstructionHistory → AcademicSurface
academicProjection masteryWithVoice = sameMastery
academicProjection masteryWithoutVoice = sameMastery

voiceProjection : InstructionHistory → VoiceSurface
voiceProjection masteryWithVoice = voice
voiceProjection masteryWithoutVoice = noVoice

voiceDiffers :
  voiceProjection masteryWithVoice ≡
  voiceProjection masteryWithoutVoice → ⊥
voiceDiffers ()

academicDoesNotDetermineVoiceWitness :
  INF.NonFactorabilityWitness academicProjection voiceProjection
academicDoesNotDetermineVoiceWitness =
  INF.nonFactorabilityWitness
    masteryWithVoice masteryWithoutVoice refl voiceDiffers

academicDoesNotDetermineVoice :
  INF.FactorsThrough academicProjection voiceProjection → ⊥
academicDoesNotDetermineVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    academicDoesNotDetermineVoiceWitness

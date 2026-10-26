module DASHI.Education.FollowThroughObserverRefinementExact where

-- Independent mathematical extension, not student records or evaluated
-- instructional effects. Credit: Johl Brown (research direction);
-- OpenAI ChatGPT (formalisation assistance).
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.FollowThroughStandaloneNonFactorabilityExact as FT

-- No deterministic relabeling, rescaling or scoring of mastery alone
-- can reconstruct the distinction in learner voice.
noScoreRechartCanRecoverVoice :
  ∀ {NewScore : Set} →
  (rechart : FT.AcademicSurface → NewScore) →
  INF.FactorsThrough
    (λ h → rechart (FT.academicProjection h)) FT.voiceProjection →
  ⊥
noScoreRechartCanRecoverVoice rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart FT.academicDoesNotDetermineVoiceWitness

-- Adding learner voice to the observer is sufficient for this PARTICULAR
-- question. This does not establish sufficiency for any other outcome,
-- participant group, pedagogy, or longer educational history.
refinedObserver : FT.InstructionHistory →
  Σ FT.AcademicSurface (λ _ → FT.VoiceSurface)
refinedObserver h = FT.academicProjection h , FT.voiceProjection h

refinedInterpretVoice :
  Σ FT.AcademicSurface (λ _ → FT.VoiceSurface) → FT.VoiceSurface
refinedInterpretVoice (_ , v) = v

refinedObserverPaysVoice :
  INF.FactorsThrough refinedObserver FT.voiceProjection
refinedObserverPaysVoice =
  INF.factorsThrough refinedInterpretVoice (λ _ → refl)

-- The repair is genuinely informative on the previously collided pair.
refinementSeparatesPair :
  refinedObserver FT.masteryWithVoice ≡
  refinedObserver FT.masteryWithoutVoice → ⊥
refinementSeparatesPair ()

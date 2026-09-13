module DASHI.Culture.CohnTechnostrategicDiscourseExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as Intersectional
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LacanIrigaray
import DASHI.Culture.CohnTechnostrategicSourceAtlasExact as CohnSources
import DASHI.Culture.FoucaultFourfoldRetreatPrimarySourceBoundaryExact as Foucault
import DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact as Philosophy
import DASHI.Governance.FeministRecognitionAuthorityCrossPollinationExact as FeministRecognition

------------------------------------------------------------------------
-- COHN / TECHNOSTRATEGIC DISCOURSE / CONSUMER ADEQUACY
--
-- Carol Cohn's 1987 article is the source-bound nuclear-strategy fixture.
-- The finite carrier and proofs below are DASHI constructions.
--
-- Core separation:
--
--   material/situated world
--      -> technostrategic representation
--      -> internally admissible strategic reasoning
--
-- does not imply that every human/material query factors through the
-- technostrategic representation.
------------------------------------------------------------------------

data StrategicSituation : Set where
  lowSituatedHarm : StrategicSituation
  highSituatedHarm : StrategicSituation

data TechnostrategicCode : Set where
  sameStrategicCode : TechnostrategicCode

data HumanMaterialConsequence : Set where
  boundedHumanMaterialConsequence : HumanMaterialConsequence
  severeHumanMaterialConsequence : HumanMaterialConsequence

data InstitutionalPowerContext : Set where
  contestableReviewContext : InstitutionalPowerContext
  insulatedExpertContext : InstitutionalPowerContext

technostrategicProjection : StrategicSituation → TechnostrategicCode
technostrategicProjection lowSituatedHarm = sameStrategicCode
technostrategicProjection highSituatedHarm = sameStrategicCode

humanMaterialConsequence : StrategicSituation → HumanMaterialConsequence
humanMaterialConsequence lowSituatedHarm = boundedHumanMaterialConsequence
humanMaterialConsequence highSituatedHarm = severeHumanMaterialConsequence

institutionalPowerContext : StrategicSituation → InstitutionalPowerContext
institutionalPowerContext lowSituatedHarm = contestableReviewContext
institutionalPowerContext highSituatedHarm = insulatedExpertContext

humanConsequenceDiffers :
  humanMaterialConsequence lowSituatedHarm
  ≡ humanMaterialConsequence highSituatedHarm → ⊥
humanConsequenceDiffers ()

canonicalHumanConsequenceCollision :
  Intersectional.NonFactorabilityWitness
    technostrategicProjection
    humanMaterialConsequence
canonicalHumanConsequenceCollision =
  Intersectional.nonFactorabilityWitness
    lowSituatedHarm
    highSituatedHarm
    refl
    humanConsequenceDiffers

technostrategicSurfaceCannotDetermineHumanConsequence :
  Intersectional.FactorsThrough
    technostrategicProjection
    humanMaterialConsequence → ⊥
technostrategicSurfaceCannotDetermineHumanConsequence =
  Intersectional.witnessRulesOutEveryFlatFactorisation
    canonicalHumanConsequenceCollision

------------------------------------------------------------------------
-- Rewording/reweighting the already-coarse code cannot restore the erased
-- consequence coordinate.  The repair must add information.
------------------------------------------------------------------------

technostrategicRechartingCannotRecoverHumanConsequence :
  ∀ {Recharted : Set} →
  (rechart : TechnostrategicCode → Recharted) →
  Intersectional.FactorsThrough
    (λ state → rechart (technostrategicProjection state))
    humanMaterialConsequence → ⊥
technostrategicRechartingCannotRecoverHumanConsequence rechart =
  Intersectional.rechartingCannotRecoverErasedPhenomenon
    rechart canonicalHumanConsequenceCollision

------------------------------------------------------------------------
-- Constructive observer refinement.
------------------------------------------------------------------------

EnrichedObservation : Set
EnrichedObservation =
  TechnostrategicCode ×
    (HumanMaterialConsequence × InstitutionalPowerContext)

enrichedObservation : StrategicSituation → EnrichedObservation
enrichedObservation state =
  technostrategicProjection state ,
    (humanMaterialConsequence state , institutionalPowerContext state)

enrichedObserverSeparatesCanonicalPair :
  enrichedObservation lowSituatedHarm
  ≡ enrichedObservation highSituatedHarm → ⊥
enrichedObserverSeparatesCanonicalPair ()

humanConsequenceFactorsThroughEnrichedObserver :
  Intersectional.FactorsThrough enrichedObservation humanMaterialConsequence
humanConsequenceFactorsThroughEnrichedObserver =
  Intersectional.factorsThrough
    (λ { (_ , (consequence , _)) → consequence })
    (λ { lowSituatedHarm → refl ; highSituatedHarm → refl })

------------------------------------------------------------------------
-- Cross-pollination reuses existing theorem/source boundaries without merging
-- their historical registers.
------------------------------------------------------------------------

foucaultPluralTechnologyReceipt : Foucault.FoucaultSourceReceipt
foucaultPluralTechnologyReceipt = Foucault.technologiesPluralityReceipt

lacanIrigarayGrammarBoundary : LacanIrigaray.LacanIrigarayGrammarBoundary
lacanIrigarayGrammarBoundary =
  LacanIrigaray.canonicalLacanIrigarayGrammarBoundary

feministRecognitionBoundary :
  FeministRecognition.FeministRecognitionCrossPollinationBoundary
feministRecognitionBoundary =
  FeministRecognition.canonicalFeministRecognitionCrossPollinationBoundary

sourceToDASHITheoremPromotion : Philosophy.PhilosophyPromotionKind
sourceToDASHITheoremPromotion = Philosophy.sourcePropositionToDASHITheorem

cohnSourceAtlas : CohnSources.CohnSourceBoundary
cohnSourceAtlas = CohnSources.canonicalCohnSourceBoundary

------------------------------------------------------------------------
-- WrongType / no-promotion boundary.
------------------------------------------------------------------------

record CohnTechnostrategicBoundary : Set where
  constructor cohnTechnostrategicBoundary
  field
    technicalCoherenceImpliesUniversalConsumerAdequacy : Bool
    technicalCoherenceImpliesUniversalConsumerAdequacyIsFalse :
      technicalCoherenceImpliesUniversalConsumerAdequacy ≡ false
    genderedMetaphorProvesPolicyCause : Bool
    genderedMetaphorProvesPolicyCauseIsFalse :
      genderedMetaphorProvesPolicyCause ≡ false
    cohnSourceMakesFoucaultOrLacanTheorem : Bool
    cohnSourceMakesFoucaultOrLacanTheoremIsFalse :
      cohnSourceMakesFoucaultOrLacanTheorem ≡ false
    crossPollinationMeansHistoricalTheoryIdentity : Bool
    crossPollinationMeansHistoricalTheoryIdentityIsFalse :
      crossPollinationMeansHistoricalTheoryIdentity ≡ false
    expertFluencyImpliesHumanConsequenceAdequacy : Bool
    expertFluencyImpliesHumanConsequenceAdequacyIsFalse :
      expertFluencyImpliesHumanConsequenceAdequacy ≡ false
    sameVocabularyImpliesSameRelationalGrammar : Bool
    sameVocabularyImpliesSameRelationalGrammarIsFalse :
      sameVocabularyImpliesSameRelationalGrammar ≡ false
    discourseAnalysisExhaustsMaterialInstitutionalAnalysis : Bool
    discourseAnalysisExhaustsMaterialInstitutionalAnalysisIsFalse :
      discourseAnalysisExhaustsMaterialInstitutionalAnalysis ≡ false
    richerObserverMayRepairConsumerAdequacy : Bool
    richerObserverMayRepairConsumerAdequacyIsTrue :
      richerObserverMayRepairConsumerAdequacy ≡ true

open CohnTechnostrategicBoundary public

canonicalCohnTechnostrategicBoundary : CohnTechnostrategicBoundary
canonicalCohnTechnostrategicBoundary =
  cohnTechnostrategicBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

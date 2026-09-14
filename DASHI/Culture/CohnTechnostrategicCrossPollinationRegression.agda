module DASHI.Culture.CohnTechnostrategicCrossPollinationRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as Intersectional
import DASHI.Culture.CohnTechnostrategicDiscourseExact as Cohn
import DASHI.Culture.CohnTechnostrategicSourceAtlasExact as CohnSources
import DASHI.Culture.CohnDiscursiveAdmissibilityNaturalisationExact as Admissibility
import DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact as Reception

------------------------------------------------------------------------
-- Regression contract for the Cohn / feminist / discourse bridge.
--
-- The first tranche fixed the coarse strategic collision, constructive repair,
-- and source/authority firewalls.  The second tranche requires:
--
--   expressible != institutionally admissible != materially/situationally real
--
-- plus normalisation != adequacy and a history-qualified future-cone weld.
------------------------------------------------------------------------

coarseTechnostrategicCollision :
  Intersectional.NonFactorabilityWitness
    Cohn.technostrategicProjection
    Cohn.humanMaterialConsequence
coarseTechnostrategicCollision = Cohn.canonicalHumanConsequenceCollision

coarseSurfaceCannotDetermineHumanConsequence :
  Intersectional.FactorsThrough
    Cohn.technostrategicProjection
    Cohn.humanMaterialConsequence → ⊥
coarseSurfaceCannotDetermineHumanConsequence =
  Cohn.technostrategicSurfaceCannotDetermineHumanConsequence

mereRewordingCannotRecoverErasedConsequence :
  ∀ {Recharted : Set} →
  (rechart : Cohn.TechnostrategicCode → Recharted) →
  Intersectional.FactorsThrough
    (λ state → rechart (Cohn.technostrategicProjection state))
    Cohn.humanMaterialConsequence → ⊥
mereRewordingCannotRecoverErasedConsequence =
  Cohn.technostrategicRechartingCannotRecoverHumanConsequence

enrichedObserverSeparatesCollisionPair :
  Cohn.enrichedObservation Cohn.lowSituatedHarm
  ≡ Cohn.enrichedObservation Cohn.highSituatedHarm → ⊥
enrichedObserverSeparatesCollisionPair =
  Cohn.enrichedObserverSeparatesCanonicalPair

enrichedObserverRecoversHumanConsequence :
  Intersectional.FactorsThrough
    Cohn.enrichedObservation
    Cohn.humanMaterialConsequence
enrichedObserverRecoversHumanConsequence =
  Cohn.humanConsequenceFactorsThroughEnrichedObserver

technicalCoherenceNotUniversalAdequacy :
  Cohn.technicalCoherenceImpliesUniversalConsumerAdequacy
    Cohn.canonicalCohnTechnostrategicBoundary ≡ false
technicalCoherenceNotUniversalAdequacy = refl

genderedMetaphorNotAutomaticCausalPolicyProof :
  Cohn.genderedMetaphorProvesPolicyCause
    Cohn.canonicalCohnTechnostrategicBoundary ≡ false
genderedMetaphorNotAutomaticCausalPolicyProof = refl

cohnDoesNotImportFoucaultOrLacanAuthority :
  Cohn.cohnSourceMakesFoucaultOrLacanTheorem
    Cohn.canonicalCohnTechnostrategicBoundary ≡ false
cohnDoesNotImportFoucaultOrLacanAuthority = refl

intersectionalAnalogyNotHistoricalIdentity :
  Cohn.crossPollinationMeansHistoricalTheoryIdentity
    Cohn.canonicalCohnTechnostrategicBoundary ≡ false
intersectionalAnalogyNotHistoricalIdentity = refl

expertFluencyNotHumanConsequenceAdequacy :
  Cohn.expertFluencyImpliesHumanConsequenceAdequacy
    Cohn.canonicalCohnTechnostrategicBoundary ≡ false
expertFluencyNotHumanConsequenceAdequacy = refl

sharedVocabularyNotSharedRelationalGrammar :
  Cohn.sameVocabularyImpliesSameRelationalGrammar
    Cohn.canonicalCohnTechnostrategicBoundary ≡ false
sharedVocabularyNotSharedRelationalGrammar = refl

discourseAnalysisNotMaterialInstitutionalExhaustion :
  Cohn.discourseAnalysisExhaustsMaterialInstitutionalAnalysis
    Cohn.canonicalCohnTechnostrategicBoundary ≡ false
discourseAnalysisNotMaterialInstitutionalExhaustion = refl

------------------------------------------------------------------------
-- Expression, admissibility and reality remain distinct.
------------------------------------------------------------------------

sameExpressionCanDifferInAdmissibility :
  Admissibility.expressionProjection Admissibility.expressibleRejected
  ≡ Admissibility.expressionProjection Admissibility.expressibleAdmitted
sameExpressionCanDifferInAdmissibility = refl

expressionCannotDetermineAdmissibility :
  Intersectional.FactorsThrough
    Admissibility.expressionProjection
    Admissibility.admissibilityProjection → ⊥
expressionCannotDetermineAdmissibility =
  Admissibility.expressionSurfaceCannotDetermineAdmissibility

inadmissibilityCannotDetermineMaterialIrrelevance :
  Intersectional.FactorsThrough
    Admissibility.admissibilityProjection
    Admissibility.materialRelevanceProjection → ⊥
inadmissibilityCannotDetermineMaterialIrrelevance =
  Admissibility.admissibilityCannotDetermineMaterialRelevance

unexpressibleCanStillBeMateriallyRelevant :
  Admissibility.expressionProjection Admissibility.outsideVocabularyConsequential ≡ false ×
  Admissibility.materialRelevanceProjection Admissibility.outsideVocabularyConsequential ≡ true
unexpressibleCanStillBeMateriallyRelevant = refl , refl

normalisationCannotDetermineConsumerAdequacy :
  Intersectional.FactorsThrough
    Admissibility.normalisationProjection
    Admissibility.adequacyProjection → ⊥
normalisationCannotDetermineConsumerAdequacy =
  Admissibility.normalisedPracticeCannotDetermineAdequacy

capabilityRecognitionBoundaryReused :
  Admissibility.recognitionLegibilityBoundary
  ≡ Admissibility.recognitionLegibilityBoundary
capabilityRecognitionBoundaryReused = refl

------------------------------------------------------------------------
-- Dynamic/history-qualified weld.
-- The existing reception owner proves that the same present vocabulary can
-- hide distinct future cones.  The Cohn bridge must expose that result rather
-- than treating today's expert vocabulary as a complete dynamics state.
------------------------------------------------------------------------

samePresentVocabularyCannotDetermineFutureCone :
  Intersectional.FactorsThrough
    Reception.presentSurface Reception.futureCode → ⊥
samePresentVocabularyCannotDetermineFutureCone =
  Admissibility.presentVocabularyCannotDetermineInstitutionalFutureCone

secondCohnSourceDoesNotCreateAuthority :
  Source.citationCreatesAuthority CohnSources.cohnWarsWimpsWomen ≡ false
secondCohnSourceDoesNotCreateAuthority = refl

cohnSourceCountIsTwo :
  Source.sourceCount (Source.sources CohnSources.cohnTechnostrategicAtlas)
  ≡ suc (suc zero)
cohnSourceCountIsTwo = refl

cohnCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority CohnSources.cohnSexAndDeath ≡ false
cohnCitationDoesNotCreateAuthority = refl

cohnCitationDoesNotImportProof :
  Source.citationImportsProof CohnSources.cohnSexAndDeath ≡ false
cohnCitationDoesNotImportProof = refl

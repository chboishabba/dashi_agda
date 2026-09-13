module DASHI.Culture.CohnTechnostrategicCrossPollinationRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as Intersectional
import DASHI.Culture.CohnTechnostrategicDiscourseExact as Cohn
import DASHI.Culture.CohnTechnostrategicSourceAtlasExact as CohnSources

------------------------------------------------------------------------
-- Regression contract for the Cohn / feminist / discourse bridge.
--
-- This contract was written before the production owners.  It therefore fixes
-- the desired collision, repair and no-promotion surface independently of the
-- implementation.  Kernel certification is tracked separately from that TDD
-- ordering and is not inferred from the existence of this file.
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

cohnCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority CohnSources.cohnSexAndDeath ≡ false
cohnCitationDoesNotCreateAuthority = refl

cohnCitationDoesNotImportProof :
  Source.citationImportsProof CohnSources.cohnSexAndDeath ≡ false
cohnCitationDoesNotImportProof = refl

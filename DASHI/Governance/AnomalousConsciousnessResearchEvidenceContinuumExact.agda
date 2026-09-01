module DASHI.Governance.AnomalousConsciousnessResearchEvidenceContinuumExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.InstitutionalAnomalousAlteredStateProgramAtlasExact as Atlas

------------------------------------------------------------------------
-- ANOMALOUS CONSCIOUSNESS / PSI / ALTERED-STATE RESEARCH CONTINUUM
--
-- Academic and clinical research are not collapsed into intelligence or
-- military programmes.  The continuum separates method, phenomenon, evidence
-- status and transferability between domains.
------------------------------------------------------------------------

data ResearchFamily : Set where
  ganzfeldPsiResearch
  freeResponsePsiResearch
  meditationResearch
  flotationRESTResearch
  hypnosisResearch
  psychedelicConsciousnessResearch
  : ResearchFamily

data MethodFamily : Set where
  controlledTargetGuessing
  freeResponseProtocol
  contemplativePractice
  restrictedEnvironmentalStimulation
  hypnoticSuggestionProtocol
  pharmacologicalAlteredStateProtocol
  : MethodFamily

data ResearchStanding : Set where
  contestedMetaAnalyticEvidence
  heterogeneousDevelopingEvidence
  phenomenologyEstablishedMechanismIncomplete
  therapeuticSignalWithLimitations
  : ResearchStanding

record ResearchEvidenceEntry : Set where
  constructor researchEvidenceEntry
  field
    family : ResearchFamily
    method : MethodFamily
    standing : ResearchStanding
    sourceReference : String
    scopeReference : String

open ResearchEvidenceEntry public

ganzfeldEntry : ResearchEvidenceEntry
ganzfeldEntry = researchEvidenceEntry
  ganzfeldPsiResearch
  controlledTargetGuessing
  contestedMetaAnalyticEvidence
  "Psychological Bulletin ganzfeld/meta-analysis literature"
  "published meta-analyses reach conflicting interpretations; this owner records contested evidence rather than declaring psi settled"

freeResponseEntry : ResearchEvidenceEntry
freeResponseEntry = researchEvidenceEntry
  freeResponsePsiResearch
  freeResponseProtocol
  contestedMetaAnalyticEvidence
  "Psychological Bulletin free-response/ganzfeld meta-analysis literature"
  "statistical anomalies and methodological interpretation remain separate claims"

meditationEntry : ResearchEvidenceEntry
meditationEntry = researchEvidenceEntry
  meditationResearch
  contemplativePractice
  heterogeneousDevelopingEvidence
  "peer-reviewed meditation neuroscience reviews/meta-analyses"
  "meditation styles and neurophenomenology are heterogeneous; observed correlates do not collapse distinct practices"

flotationEntry : ResearchEvidenceEntry
flotationEntry = researchEvidenceEntry
  flotationRESTResearch
  restrictedEnvironmentalStimulation
  therapeuticSignalWithLimitations
  "systematic review of flotation-REST research"
  "evidence includes relaxation/anxiety/pain signals with methodological and generalisability limitations"

hypnosisEntry : ResearchEvidenceEntry
hypnosisEntry = researchEvidenceEntry
  hypnosisResearch
  hypnoticSuggestionProtocol
  phenomenologyEstablishedMechanismIncomplete
  "non-ordinary-state / hypnosis research literature"
  "hypnosis is studied as an altered-state/suggestion method; that does not validate historical mind-control claims"

psychedelicConsciousnessEntry : ResearchEvidenceEntry
psychedelicConsciousnessEntry = researchEvidenceEntry
  psychedelicConsciousnessResearch
  pharmacologicalAlteredStateProtocol
  heterogeneousDevelopingEvidence
  "psychedelic phenomenology and neuroscience literature"
  "psychedelic and meditative self-alteration can overlap phenomenologically while remaining distinct induction methods"

------------------------------------------------------------------------
-- Same 'altered consciousness' observer cannot recover induction method or
-- evidential standing.
------------------------------------------------------------------------

data CoarseAlteredStateSurface : Set where
  alteredConsciousnessSurface : CoarseAlteredStateSurface

data ConsciousnessWorld : Set where
  meditationWorld psychedelicWorld ganzfeldWorld : ConsciousnessWorld

coarseSurface : ConsciousnessWorld → CoarseAlteredStateSurface
coarseSurface _ = alteredConsciousnessSurface

inductionMethod : ConsciousnessWorld → MethodFamily
inductionMethod meditationWorld = contemplativePractice
inductionMethod psychedelicWorld = pharmacologicalAlteredStateProtocol
inductionMethod ganzfeldWorld = controlledTargetGuessing

standingAt : ConsciousnessWorld → ResearchStanding
standingAt meditationWorld = heterogeneousDevelopingEvidence
standingAt psychedelicWorld = heterogeneousDevelopingEvidence
standingAt ganzfeldWorld = contestedMetaAnalyticEvidence

methodDiffers : inductionMethod meditationWorld ≡ inductionMethod psychedelicWorld → ⊥
methodDiffers ()

coarseAlteredStateCannotRecoverMethod :
  INF.FactorsThrough coarseSurface inductionMethod → ⊥
coarseAlteredStateCannotRecoverMethod =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness meditationWorld psychedelicWorld refl methodDiffers)

------------------------------------------------------------------------
-- Transfer gates.
------------------------------------------------------------------------

data MeditationEvidencePromotesPsi : Set where

data PsiMetaAnalysisPromotesOperationalIntelligenceUtility : Set where

data PsychedelicPhenomenologyPromotesRemoteViewing : Set where

data HypnosisResearchPromotesHistoricalMindControlEfficacy : Set where

data AlteredStateSimilarityPromotesSameMechanism : Set where

meditationEvidenceDoesNotPromotePsi : MeditationEvidencePromotesPsi → ⊥
meditationEvidenceDoesNotPromotePsi ()

psiMetaAnalysisDoesNotPromoteOperationalUtility :
  PsiMetaAnalysisPromotesOperationalIntelligenceUtility → ⊥
psiMetaAnalysisDoesNotPromoteOperationalUtility ()

psychedelicPhenomenologyDoesNotPromoteRemoteViewing :
  PsychedelicPhenomenologyPromotesRemoteViewing → ⊥
psychedelicPhenomenologyDoesNotPromoteRemoteViewing ()

hypnosisResearchDoesNotPromoteHistoricalMindControlEfficacy :
  HypnosisResearchPromotesHistoricalMindControlEfficacy → ⊥
hypnosisResearchDoesNotPromoteHistoricalMindControlEfficacy ()

alteredStateSimilarityDoesNotPromoteSameMechanism :
  AlteredStateSimilarityPromotesSameMechanism → ⊥
alteredStateSimilarityDoesNotPromoteSameMechanism ()

atlasBoundary : Atlas.InstitutionalAnomalousAlteredStateAtlasBoundary
atlasBoundary = Atlas.canonicalInstitutionalAnomalousAlteredStateAtlasBoundary

record AnomalousConsciousnessResearchBoundary : Set where
  constructor anomalousConsciousnessResearchBoundary
  field
    alteredStateIsMultiMethod : Bool
    alteredStateIsMultiMethodIsTrue : alteredStateIsMultiMethod ≡ true
    academicPsiEqualsOperationalIntelligenceUtility : Bool
    academicPsiEqualsOperationalIntelligenceUtilityIsFalse :
      academicPsiEqualsOperationalIntelligenceUtility ≡ false
    meditationPsychedelicOverlapMeansSameMechanism : Bool
    meditationPsychedelicOverlapMeansSameMechanismIsFalse :
      meditationPsychedelicOverlapMeansSameMechanism ≡ false
    hypnosisScienceValidatesHistoricalMindControlProgrammes : Bool
    hypnosisScienceValidatesHistoricalMindControlProgrammesIsFalse :
      hypnosisScienceValidatesHistoricalMindControlProgrammes ≡ false

canonicalAnomalousConsciousnessResearchBoundary :
  AnomalousConsciousnessResearchBoundary
canonicalAnomalousConsciousnessResearchBoundary =
  anomalousConsciousnessResearchBoundary
    true refl false refl false refl false refl

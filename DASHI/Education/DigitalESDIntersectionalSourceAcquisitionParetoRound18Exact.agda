module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound18Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- ROUND 18: TRACE-GOVERNED CLASSIFICATION / LANGUAGE-INCIDENCE TENSION.
--
-- Post-Round-17 acquisition retains affected-but-unsampled as a P0 residual.
-- This round adds a distinct mechanism: writers may be consequentially
-- classified through their text traces even though their situated testimony is
-- absent from the detector-evaluation carrier.
--
-- Two sources are intentionally braided because their findings differ under
-- different detector families, samples and methods. DASHI preserves that
-- tension rather than manufacturing a universal fairness/unfairness verdict.
------------------------------------------------------------------------

data Round18Residual : Set where
  publicDetectorFalsePositiveByNonNativeEnglishWriting : Round18Residual
  constructedGREDetectorNoObservedNonNativeDisadvantage : Round18Residual

record Round18Candidate : Set where
  constructor round18-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    sameObjectExternalIdentityState : String
    deweyState : String
    targetResidual : Round18Residual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round18Candidate public

mkRound18Candidate :
  (source : Attr.AttributedSource) →
  String → String → Round18Residual → String → String →
  Round18Candidate
mkRound18Candidate source identityState dewey residual reading limitation =
  round18-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound18Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object publication QID recorded by round 18"))
    identityState
    dewey
    residual reading limitation false refl

------------------------------------------------------------------------
-- Liang et al. 2023: public GPT detectors show high false-positive incidence on
-- a specific non-native-English essay corpus.
------------------------------------------------------------------------

liangGPTDetectorBiasSource : Attr.AttributedSource
liangGPTDetectorBiasSource = Attr.mkDOISource
  "Weixin Liang; Mert Yüksekgönül; Yining Mao; Eric Wu; James Zou"
  "GPT detectors are biased against non-native English writers"
  "Patterns 4(7), 100779"
  "2023"
  "10.1016/j.patter.2023.100779"
  "https://doi.org/10.1016/j.patter.2023.100779"
  (Attr.namedSourceKind "Patterns opinion/news-type article with empirical benchmark analysis")
  "Source-bounded benchmark analysis of seven widely used GPT detectors using 91 TOEFL essays written by Chinese non-native English writers and 88 US eighth-grade essays. The paper reports substantially higher false-positive incidence on the TOEFL essays and discusses educational/evaluative risks for non-native writers."
  Attr.publicAttribution

liangCandidate : Round18Candidate
liangCandidate = mkRound18Candidate
  liangGPTDetectorBiasSource
  "DOI 10.1016/j.patter.2023.100779; PMID 37521038; PMCID PMC10382961; arXiv:2304.02819 retained as a distinct preprint identity"
  "Dewey classification unresolved; no nearest-label substitution"
  publicDetectorFalsePositiveByNonNativeEnglishWriting
  "High-alpha classification-incidence donor: the detector benchmark evaluates text traces produced by writers who could be affected by detector decisions, while the benchmark carrier is essays/detector outputs rather than situated writer testimony. It therefore pays affected-but-unsampled and language-incidence fibres without pretending to observe disciplinary outcomes."
  "Seven public detector systems and specific essay corpora. The reported disparity does not establish that every AI-text detector disadvantages every non-native writer, that every false positive produces sanction, or that language background is the sole causal mechanism."

------------------------------------------------------------------------
-- Jiang et al. 2024: a different detector family / GRE corpus reports no
-- evidence of disadvantage to non-native-English writers.
------------------------------------------------------------------------

jiangGREDetectorSource : Attr.AttributedSource
jiangGREDetectorSource = Attr.mkDOISource
  "Yang Jiang; Jiangang Hao; Michael Fauss; Chen Li"
  "Detecting ChatGPT-generated essays in a large-scale writing assessment: Is there a bias against non-native English speakers?"
  "Computers & Education 217, 105070"
  "2024"
  "10.1016/j.compedu.2024.105070"
  "https://doi.org/10.1016/j.compedu.2024.105070"
  Attr.academicArticleSource
  "Empirical large-scale writing-assessment study using GRE essay data and detector approaches based on e-rater linguistic features and perplexity. Within the reported study design, the authors report near-perfect classification performance and no evidence that the constructed detectors disadvantaged non-native English speakers."
  Attr.publicAttribution

jiangCandidate : Round18Candidate
jiangCandidate = mkRound18Candidate
  jiangGREDetectorSource
  "DOI 10.1016/j.compedu.2024.105070; publication-level QID unresolved"
  "Dewey classification unresolved; no nearest-label substitution"
  constructedGREDetectorNoObservedNonNativeDisadvantage
  "Necessary counter-evidence for the same broad consumer question: detector fairness/incidence depends on detector construction, sample, task and evaluation design. A no-disadvantage result under this GRE/detector configuration prevents Liang's benchmark from being promoted into a universal detector-bias law."
  "The reported no-disadvantage result is bounded to the constructed detectors, GRE sample and evaluation conditions. It does not establish fairness of public detectors, deployed institutional workflows, sanctions, appeals, or all language groups."

canonicalRound18Frontier : List Round18Candidate
canonicalRound18Frontier = liangCandidate ∷ jiangCandidate ∷ []

------------------------------------------------------------------------
-- DASHI-owned finite tension/collision.
--
-- A coarse 'AI-text detector in educational assessment' surface can coexist
-- with materially different language-group false-positive incidence. Therefore
-- the coarse surface cannot recover the incidence required by the consumer.
------------------------------------------------------------------------

data DetectorIncidenceWorld : Set where
  detectorSurfaceLanguageDisparityObserved : DetectorIncidenceWorld
  detectorSurfaceNoLanguageDisparityObserved : DetectorIncidenceWorld

data CoarseDetectorSurface : Set where
  sameEducationalAITextDetection : CoarseDetectorSurface

coarseDetectorProjection : DetectorIncidenceWorld → CoarseDetectorSurface
coarseDetectorProjection detectorSurfaceLanguageDisparityObserved = sameEducationalAITextDetection
coarseDetectorProjection detectorSurfaceNoLanguageDisparityObserved = sameEducationalAITextDetection

languageGroupIncidenceDiffers : DetectorIncidenceWorld → Bool
languageGroupIncidenceDiffers detectorSurfaceLanguageDisparityObserved = true
languageGroupIncidenceDiffers detectorSurfaceNoLanguageDisparityObserved = false

languageGroupIncidenceReallyDiffers :
  languageGroupIncidenceDiffers detectorSurfaceLanguageDisparityObserved ≡
  languageGroupIncidenceDiffers detectorSurfaceNoLanguageDisparityObserved → ⊥
languageGroupIncidenceReallyDiffers ()

detectorIncidenceWitness :
  Intersection.NonFactorabilityWitness coarseDetectorProjection languageGroupIncidenceDiffers
detectorIncidenceWitness =
  Intersection.nonFactorabilityWitness
    detectorSurfaceLanguageDisparityObserved
    detectorSurfaceNoLanguageDisparityObserved
    refl languageGroupIncidenceReallyDiffers

DetectorIncidenceFactorisation : Set
DetectorIncidenceFactorisation =
  Intersection.FactorsThrough coarseDetectorProjection languageGroupIncidenceDiffers

detectorIncidenceDoesNotFactorThroughCoarseDetectorSurface :
  DetectorIncidenceFactorisation → ⊥
detectorIncidenceDoesNotFactorThroughCoarseDetectorSurface =
  Intersection.witnessRulesOutEveryFlatFactorisation detectorIncidenceWitness

------------------------------------------------------------------------
-- Preserved tension receipt: disagreement is source-/method-indexed, not a
-- logical contradiction and not a licence to average to a middle verdict.
------------------------------------------------------------------------

record DetectorTensionReceipt : Set where
  constructor detector-tension-receipt
  field
    leftSource : Attr.AttributedSource
    rightSource : Attr.AttributedSource
    sameBroadConsumerQuestion : Bool
    sameBroadConsumerQuestionIsTrue : sameBroadConsumerQuestion ≡ true
    detectorFamilyOrSampleMayDiffer : Bool
    detectorFamilyOrSampleMayDifferIsTrue : detectorFamilyOrSampleMayDiffer ≡ true
    universalBiasVerdictCreated : Bool
    universalBiasVerdictCreatedIsFalse : universalBiasVerdictCreated ≡ false
    universalFairnessVerdictCreated : Bool
    universalFairnessVerdictCreatedIsFalse : universalFairnessVerdictCreated ≡ false

canonicalDetectorTension : DetectorTensionReceipt
canonicalDetectorTension = detector-tension-receipt
  liangGPTDetectorBiasSource
  jiangGREDetectorSource
  true refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- No-promotion / observer / deployment firewalls.
------------------------------------------------------------------------

data Round18CandidateCreatesIncludedStudy : Set where
data TraceBenchmarkCreatesWriterTestimony : Set where
data FalsePositiveDisparityCreatesObservedSanction : Set where
data OneDetectorFamilyCreatesUniversalBiasLaw : Set where
data OneNoBiasResultCreatesUniversalDeploymentFairness : Set where
data SourceDisagreementCreatesLogicalContradiction : Set where

round18CandidateDoesNotCreateIncludedStudy :
  Round18CandidateCreatesIncludedStudy → ⊥
round18CandidateDoesNotCreateIncludedStudy ()

traceBenchmarkDoesNotCreateWriterTestimony :
  TraceBenchmarkCreatesWriterTestimony → ⊥
traceBenchmarkDoesNotCreateWriterTestimony ()

falsePositiveDisparityDoesNotCreateObservedSanction :
  FalsePositiveDisparityCreatesObservedSanction → ⊥
falsePositiveDisparityDoesNotCreateObservedSanction ()

oneDetectorFamilyDoesNotCreateUniversalBiasLaw :
  OneDetectorFamilyCreatesUniversalBiasLaw → ⊥
oneDetectorFamilyDoesNotCreateUniversalBiasLaw ()

oneNoBiasResultDoesNotCreateUniversalDeploymentFairness :
  OneNoBiasResultCreatesUniversalDeploymentFairness → ⊥
oneNoBiasResultDoesNotCreateUniversalDeploymentFairness ()

sourceDisagreementDoesNotCreateLogicalContradiction :
  SourceDisagreementCreatesLogicalContradiction → ⊥
sourceDisagreementDoesNotCreateLogicalContradiction ()

round18Reading : String
round18Reading =
  "Round 18 adds trace-governed classification as a distinct affected-but-unsampled mechanism. Liang et al. report high false-positive incidence for non-native-English TOEFL essays under seven public GPT detectors; Jiang et al. report no evidence of non-native disadvantage under a different large-scale GRE detector design. DASHI preserves both source-bounded results as a tension and owns the finite collision showing that a coarse educational AI-text-detection surface cannot recover language-group incidence. Essay/detector benchmarks do not create writer testimony, observed sanctions, universal bias laws or universal deployment fairness."

module DASHI.Law.SensibLawExpertInferenceAncestryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- EXPERT INFERENCE ANCESTRY
--
-- Thin child of the repo-wide source-genealogy / dependency idea:
-- distinct documents and agreement do not imply independent generation paths.
-- For expert evidence, an additional coordinate is whether a later inference
-- was formed independently, after exposure to an earlier opinion, or through an
-- unresolved ancestry path.
--
-- This owner deliberately does NOT import the Wikimedia parent ontology.  The
-- parent relationship is recorded below as structural precedent only.  The law
-- layer reuses generic query adequacy, observer refinement and attributed-source
-- machinery directly.
--
-- Crucial two-sided correction:
--   prior-opinion exposure != proved causal dependence;
--   separate reports / agreement != proved independent inference.
------------------------------------------------------------------------

record ParentStructuralPrecedent : Set where
  constructor parentStructuralPrecedentRecord
  field
    parentOwner : String
    parentRole : String
    sameHistoricalDoctrineClaimed : Bool
    parentCitationCreatesLegalAuthority : Bool

open ParentStructuralPrecedent public

parentStructuralPrecedent : ParentStructuralPrecedent
parentStructuralPrecedent =
  parentStructuralPrecedentRecord
    "DASHI.Wikimedia.IbrahimSnowballMemoryRepetitionSourceDependencyConsensusBidiExact"
    "structural precedent: repeated/agreed outputs do not recover source independence; expert inference ancestry is a downstream consumer-specific specialization"
    false
    false

------------------------------------------------------------------------
-- Source attribution.
--
-- Pilditch/Hahn/Lagnado support only the general evidential-dependency point.
-- The paper is not represented as an Australian family-law standard, a rule of
-- evidence, or proof that any particular expert report is dependent.
------------------------------------------------------------------------

pilditchDependencySource : Attribution.AttributedSource
pilditchDependencySource = Attribution.mkDOISource
  "Toby D. Pilditch; Ulrike Hahn; David Lagnado"
  "The problem of dependency"
  "Synthese 205, article 143"
  "2025"
  "10.1007/s11229-025-04969-w"
  "https://doi.org/10.1007/s11229-025-04969-w"
  Attribution.academicArticleSource
  "supports the bounded general distinction between multiplicity and evidential independence; does not establish expert-specific causal dependence, legal breach, admissibility, or legal authority"
  Attribution.publicAttribution

inferenceAncestrySourceAtlas : Attribution.AttributedSourceAtlas
inferenceAncestrySourceAtlas = Attribution.mkSourceAtlas
  "SensibLaw expert inference ancestry source atlas"
  "DASHI.Law.SensibLawExpertInferenceAncestryExact"
  (pilditchDependencySource ∷ [])
  "general evidential-dependency source only; Australian professional standards and case application remain separate downstream payments"

------------------------------------------------------------------------
-- Explicit exposure receipt.  Exposure timing is retained separately from any
-- conclusion about causal influence.
------------------------------------------------------------------------

data PriorOpinionExposureTiming : Set where
  beforeOwnViewFormed : PriorOpinionExposureTiming
  afterOwnViewFormed : PriorOpinionExposureTiming
  exposureTimingUnresolved : PriorOpinionExposureTiming

data ExposureDisclosure : Set where
  exposureDisclosed : ExposureDisclosure
  exposureNotDisclosed : ExposureDisclosure
  disclosureUnresolved : ExposureDisclosure

record PriorOpinionExposureReceipt : Set where
  constructor priorOpinionExposureReceipt
  field
    laterReportReference : String
    priorOpinionReference : String
    exposureTiming : PriorOpinionExposureTiming
    reasonReference : String
    disclosure : ExposureDisclosure

------------------------------------------------------------------------
-- Exact finite witness 1: nominally separate agreeing reports cannot recover
-- independent inference ancestry.
------------------------------------------------------------------------

data InferenceAncestryWorld : Set where
  agreeingIndependentInferencePaths : InferenceAncestryWorld
  agreeingInheritedInferencePath : InferenceAncestryWorld

data NominalReportAgreementSurface : Set where
  twoDistinctReportsAgree : NominalReportAgreementSurface

data InferenceAncestryCoordinate : Set where
  independentInferenceAncestry : InferenceAncestryCoordinate
  inheritedOrDependentInferenceAncestry : InferenceAncestryCoordinate

data InferenceAncestryQuery : Set where
  nominalAgreementQuery : InferenceAncestryQuery
  independentAncestryQuery : InferenceAncestryQuery

data InferenceAncestryAnswer : Set where
  agreementObserved : InferenceAncestryAnswer
  independentAncestryAnswer : InferenceAncestryAnswer
  dependentAncestryAnswer : InferenceAncestryAnswer

nominalReportAgreementSurface :
  InferenceAncestryWorld → NominalReportAgreementSurface
nominalReportAgreementSurface world = twoDistinctReportsAgree

inferenceAncestryCoordinate :
  InferenceAncestryWorld → InferenceAncestryCoordinate
inferenceAncestryCoordinate agreeingIndependentInferencePaths =
  independentInferenceAncestry
inferenceAncestryCoordinate agreeingInheritedInferencePath =
  inheritedOrDependentInferenceAncestry

inferenceAncestryAnswer :
  InferenceAncestryQuery → InferenceAncestryWorld → InferenceAncestryAnswer
inferenceAncestryAnswer nominalAgreementQuery world = agreementObserved
inferenceAncestryAnswer independentAncestryQuery agreeingIndependentInferencePaths =
  independentAncestryAnswer
inferenceAncestryAnswer independentAncestryQuery agreeingInheritedInferencePath =
  dependentAncestryAnswer

inferenceAncestrySemantics :
  Query.QuerySemantics
    InferenceAncestryWorld
    InferenceAncestryQuery
    InferenceAncestryAnswer
inferenceAncestrySemantics = Query.querySemantics inferenceAncestryAnswer

nominalAgreementQueryAdequate :
  Query.AdequateFor
    nominalReportAgreementSurface
    inferenceAncestrySemantics
    nominalAgreementQuery
nominalAgreementQueryAdequate =
  Query.factorsForQuery
    (λ surface → agreementObserved)
    (λ world → refl)

InferenceAncestryQueryAdequacyDefect : Set₁
InferenceAncestryQueryAdequacyDefect =
  Query.QueryAdequacyDefect
    nominalReportAgreementSurface
    inferenceAncestrySemantics
    independentAncestryQuery

inferenceAncestryQueryAdequacyDefect : InferenceAncestryQueryAdequacyDefect
inferenceAncestryQueryAdequacyDefect =
  Query.queryAdequacyDefect
    agreeingIndependentInferencePaths
    agreeingInheritedInferencePath
    refl
    (λ ())

InferenceAncestryQueryAdequate : Set₁
InferenceAncestryQueryAdequate =
  Query.AdequateFor
    nominalReportAgreementSurface
    inferenceAncestrySemantics
    independentAncestryQuery

inferenceAncestryQueryNotAdequate :
  InferenceAncestryQueryAdequate → ⊥
inferenceAncestryQueryNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    inferenceAncestryQueryAdequacyDefect

------------------------------------------------------------------------
-- Constructive repair: retain agreement AND ancestry.  This is a strict
-- refinement for the declared two-world specimen, not a universal sufficiency
-- theorem for expert-evidence evaluation.
------------------------------------------------------------------------

reportAgreementPlusInferenceAncestry :
  InferenceAncestryWorld →
  NominalReportAgreementSurface × InferenceAncestryCoordinate
reportAgreementPlusInferenceAncestry =
  Observer.pairObserver nominalReportAgreementSurface inferenceAncestryCoordinate

reportAgreementPlusInferenceAncestryRefinesAgreement :
  Observer.Refines
    nominalReportAgreementSurface
    reportAgreementPlusInferenceAncestry
reportAgreementPlusInferenceAncestryRefinesAgreement =
  Observer.pairRefinesLeft
    nominalReportAgreementSurface
    inferenceAncestryCoordinate

reportAgreementPlusInferenceAncestryStrictRefinement :
  Observer.StrictRefinement
    nominalReportAgreementSurface
    reportAgreementPlusInferenceAncestry
reportAgreementPlusInferenceAncestryStrictRefinement =
  Observer.strictPairRefinement
    nominalReportAgreementSurface
    inferenceAncestryCoordinate
    agreeingIndependentInferencePaths
    agreeingInheritedInferencePath
    refl
    (λ ())

------------------------------------------------------------------------
-- Exact finite witness 2: observed prior-opinion exposure does not by itself
-- recover whether the earlier opinion actually influenced the later inference.
------------------------------------------------------------------------

data ExposureInfluenceWorld : Set where
  exposedButIndependentReasoning : ExposureInfluenceWorld
  exposedAndInfluencedReasoning : ExposureInfluenceWorld

data ExposureSurface : Set where
  priorOpinionReadBeforeFinalisation : ExposureSurface

data InfluenceCoordinate : Set where
  noCausalInfluenceEstablished : InfluenceCoordinate
  causalInfluencePresent : InfluenceCoordinate

priorOpinionExposureSurface : ExposureInfluenceWorld → ExposureSurface
priorOpinionExposureSurface world = priorOpinionReadBeforeFinalisation

influenceCoordinate : ExposureInfluenceWorld → InfluenceCoordinate
influenceCoordinate exposedButIndependentReasoning = noCausalInfluenceEstablished
influenceCoordinate exposedAndInfluencedReasoning = causalInfluencePresent

exposureCannotRecoverInfluence :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    priorOpinionExposureSurface
    influenceCoordinate → ⊥
exposureCannotRecoverInfluence =
  DASHI.Core.IntersectionalNonFactorability.witnessRulesOutEveryFlatFactorisation
    (DASHI.Core.IntersectionalNonFactorability.nonFactorabilityWitness
      exposedButIndependentReasoning
      exposedAndInfluencedReasoning
      refl
      (λ ()))

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data PriorOpinionExposureMeansNoEvidence : Set where
data SeparateDocumentsAutomaticallyIndependentInference : Set where
data AgreementAutomaticallyIndependentInference : Set where
data PriorOpinionExposureAutomaticallyProvesCausalDependence : Set where
data NoRecordedExposureAutomaticallyIndependentInference : Set where
data CitationCreatesLegalAuthority : Set where

priorOpinionExposureDoesNotMeanNoEvidence :
  PriorOpinionExposureMeansNoEvidence → ⊥
priorOpinionExposureDoesNotMeanNoEvidence ()

separateDocumentsDoNotAutomaticallyProveIndependentInference :
  SeparateDocumentsAutomaticallyIndependentInference → ⊥
separateDocumentsDoNotAutomaticallyProveIndependentInference ()

agreementDoesNotAutomaticallyProveIndependentInference :
  AgreementAutomaticallyIndependentInference → ⊥
agreementDoesNotAutomaticallyProveIndependentInference ()

priorOpinionExposureDoesNotAutomaticallyProveCausalDependence :
  PriorOpinionExposureAutomaticallyProvesCausalDependence → ⊥
priorOpinionExposureDoesNotAutomaticallyProveCausalDependence ()

noRecordedExposureDoesNotAutomaticallyProveIndependentInference :
  NoRecordedExposureAutomaticallyIndependentInference → ⊥
noRecordedExposureDoesNotAutomaticallyProveIndependentInference ()

citationDoesNotCreateLegalAuthority : CitationCreatesLegalAuthority → ⊥
citationDoesNotCreateLegalAuthority ()

record ExpertInferenceAncestryBoundary : Set where
  constructor expertInferenceAncestryBoundary
  field
    separateDocumentsProveIndependentInference : Bool
    agreementProvesIndependentInference : Bool
    exposureProvesCausalDependence : Bool
    noRecordedExposureProvesIndependence : Bool
    exposureErasesAllEvidentialValue : Bool
    ancestryRequiresOwnCoordinate : Bool
    joinedObserverMayRepairDeclaredAncestryLoss : Bool
    citationCreatesLegalAuthorityFlag : Bool
    parentStructuralPrecedentRetained : Bool

open ExpertInferenceAncestryBoundary public

canonicalExpertInferenceAncestryBoundary : ExpertInferenceAncestryBoundary
canonicalExpertInferenceAncestryBoundary =
  expertInferenceAncestryBoundary
    false false false false false true true false true

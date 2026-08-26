module DASHI.Biology.AutisticInformationProcessingLandscapeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection

------------------------------------------------------------------------
-- POSITIVE AUTISM / INFORMATION-PROCESSING LANDSCAPE
--
-- This module deliberately accepts a diagnostic-group coordinate as a valid
-- research coordinate.  It does not attempt to re-litigate diagnostic
-- ontology.  Its narrower point is that a positive scientific account of
-- autistic difference need not identify autism with one static connectome or
-- one scalar deficit.  The literature motivates keeping distinct observer
-- axes for network organization, memory, processing, learning, development,
-- perturbational response, and situated/intersectional context.
--
-- The finite dynamics below are DASHI synthetic witnesses.  They prove only
-- logical non-collapse statements.  No transition table is attributed to the
-- cited empirical literature.
------------------------------------------------------------------------

record LiteratureSource : Set where
  constructor literatureSource
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    role : String

open LiteratureSource public

landscapeSources : List LiteratureSource
landscapeSources =
  literatureSource
    "Tobias P. Whelan et al."
    "The 'PSILAUT' protocol: an experimental medicine study of autistic differences in the function of brain serotonin targets of psilocybin"
    "BMC Psychiatry 24:319"
    2024
    "10.1186/s12888-024-05768-2"
    "perturbational shiftability / serotonin-system motivation" ∷
  literatureSource
    "Xinyun Lin; Simin Deng; Xiuhong Li"
    "Multilevel Resting-State Dysfunctional Connectivity in People With Autism Spectrum Disorder: A Systematic Review and Meta-Analysis"
    "Autism Research 18(12):2463-2477"
    2025
    "10.1002/aur.70128"
    "resting-state connectivity differences with historically elusive consistency" ∷
  literatureSource
    "Tjasa Velikonja; Anne-Kathrin Fett; Eva Velthorst"
    "Patterns of Nonsocial and Social Cognitive Functioning in Adults With Autism Spectrum Disorder: A Systematic Review and Meta-analysis"
    "JAMA Psychiatry 76(2):135-151"
    2019
    "10.1001/jamapsychiatry.2018.3645"
    "processing-speed and learning/memory profile rather than one global cognitive scalar" ∷
  literatureSource
    "Kangjie Geng; Yan Wang; Wangqian Fu; Siting Chen; Yuqi Yang"
    "Episodic memory impairment and its influencing factors in individuals with autism spectrum disorder: systematic review and meta-analysis"
    "European Archives of Psychiatry and Clinical Neuroscience"
    2024
    "10.1007/s00406-024-01889-7"
    "episodic-memory heterogeneity and task/developmental moderation" ∷
  literatureSource
    "Rebecca R. Bell; Hannah R. Thomas; Jenny R. Saffran; Inge-Marie Eigsti"
    "A systematic review of statistical learning in autism spectrum disorder"
    "Molecular Autism 17:2"
    2026
    "10.1186/s13229-025-00697-7"
    "mixed/minimal behavioral statistical-learning differences with variable neural implementation" ∷
  literatureSource
    "Kelly Mo et al."
    "Sex/gender differences in the human autistic brains: A systematic review of 20 years of neuroimaging research"
    "NeuroImage: Clinical 32:102811"
    2021
    "10.1016/j.nicl.2021.102811"
    "sex/gender modulation and historical male-sample bias in neuroimaging" ∷
  literatureSource
    "Nathan V. Mallipeddi; Rachel A. VanDaalen"
    "Intersectionality Within Critical Autism Studies: A Narrative Review"
    "Autism in Adulthood 4(4):281-289"
    2022
    "10.1089/aut.2021.0014"
    "intersectionality as non-additive situated analytical context" ∷ []

------------------------------------------------------------------------
-- Candidate multiaxial carrier.
------------------------------------------------------------------------

data DiagnosticCategory : Set where
  autistic nonAutistic : DiagnosticCategory

data MemoryResidue : Set where
  weakTrace strongTrace : MemoryResidue

data ProcessingPolicy : Set where
  rapidCommit detailPreserving : ProcessingPolicy

data LearningRule : Set where
  conservativeUpdate rapidUpdate : LearningRule

data DevelopmentalStage : Set where
  earlierStage laterStage : DevelopmentalStage

data SituatedContext : Set where
  supportiveContext highDemandContext : SituatedContext

record InformationProcessingState : Set where
  constructor informationProcessingState
  field
    diagnosis : DiagnosticCategory
    memory : MemoryResidue
    processing : ProcessingPolicy
    learning : LearningRule
    development : DevelopmentalStage
    context : SituatedContext

open InformationProcessingState public

------------------------------------------------------------------------
-- Memory is retained state that can change processing of the same present
-- input.  This is a structural witness, not a claim that either policy is a
-- universal autistic policy.
------------------------------------------------------------------------

data PresentInput : Set where
  sameInput : PresentInput

data ProcessingDisposition : Set where
  commitNow holdForMoreEvidence : ProcessingDisposition

processingDisposition :
  InformationProcessingState → PresentInput → ProcessingDisposition
processingDisposition
  (informationProcessingState d weakTrace rapidCommit l s c) sameInput = commitNow
processingDisposition
  (informationProcessingState d strongTrace rapidCommit l s c) sameInput = commitNow
processingDisposition
  (informationProcessingState d weakTrace detailPreserving l s c) sameInput = holdForMoreEvidence
processingDisposition
  (informationProcessingState d strongTrace detailPreserving l s c) sameInput = holdForMoreEvidence

memorySensitiveLeft : InformationProcessingState
memorySensitiveLeft =
  informationProcessingState
    autistic weakTrace rapidCommit conservativeUpdate earlierStage supportiveContext

memorySensitiveRight : InformationProcessingState
memorySensitiveRight =
  informationProcessingState
    autistic strongTrace detailPreserving rapidUpdate earlierStage supportiveContext

sameDiagnosisAcrossProcessingWitness :
  diagnosis memorySensitiveLeft ≡ diagnosis memorySensitiveRight
sameDiagnosisAcrossProcessingWitness = refl

samePresentInputAcrossProcessingWitness : sameInput ≡ sameInput
samePresentInputAcrossProcessingWitness = refl

processingCanDifferAtSameDiagnosisAndPresentInput :
  processingDisposition memorySensitiveLeft sameInput
    ≡ processingDisposition memorySensitiveRight sameInput → ⊥
processingCanDifferAtSameDiagnosisAndPresentInput ()

------------------------------------------------------------------------
-- Learning is represented as an update law rather than as a static score.
------------------------------------------------------------------------

learnMemory : LearningRule → MemoryResidue → PresentInput → MemoryResidue
learnMemory conservativeUpdate weakTrace sameInput = weakTrace
learnMemory conservativeUpdate strongTrace sameInput = strongTrace
learnMemory rapidUpdate weakTrace sameInput = strongTrace
learnMemory rapidUpdate strongTrace sameInput = strongTrace

learningTransition :
  InformationProcessingState → PresentInput → InformationProcessingState
learningTransition
  (informationProcessingState d m p l s c) input =
  informationProcessingState d (learnMemory l m input) p l s c

slowLearnerState : InformationProcessingState
slowLearnerState =
  informationProcessingState
    autistic weakTrace detailPreserving conservativeUpdate earlierStage supportiveContext

rapidLearnerState : InformationProcessingState
rapidLearnerState =
  informationProcessingState
    autistic weakTrace detailPreserving rapidUpdate earlierStage supportiveContext

sameDiagnosisBeforeLearning :
  diagnosis slowLearnerState ≡ diagnosis rapidLearnerState
sameDiagnosisBeforeLearning = refl

sameMemoryBeforeLearning :
  memory slowLearnerState ≡ memory rapidLearnerState
sameMemoryBeforeLearning = refl

postLearningMemoryDiffers :
  memory (learningTransition slowLearnerState sameInput)
    ≡ memory (learningTransition rapidLearnerState sameInput) → ⊥
postLearningMemoryDiffers ()

------------------------------------------------------------------------
-- Intersectionality: retaining autism as a category does not license treating
-- that single axis as sufficient for every situated outcome.  This reuses the
-- repository's canonical non-factorability theorem rather than introducing a
-- second intersectionality calculus.
------------------------------------------------------------------------

data SituatedResponse : Set where
  regulatedResponse overloadedResponse : SituatedResponse

diagnosticProjection : InformationProcessingState → DiagnosticCategory
diagnosticProjection = diagnosis

situatedResponse : InformationProcessingState → SituatedResponse
situatedResponse
  (informationProcessingState d m p l s supportiveContext) = regulatedResponse
situatedResponse
  (informationProcessingState d m p l s highDemandContext) = overloadedResponse

supportiveAutisticState : InformationProcessingState
supportiveAutisticState =
  informationProcessingState
    autistic strongTrace detailPreserving conservativeUpdate laterStage supportiveContext

highDemandAutisticState : InformationProcessingState
highDemandAutisticState =
  informationProcessingState
    autistic strongTrace detailPreserving conservativeUpdate laterStage highDemandContext

sameAcceptedDiagnosticCategory :
  diagnosticProjection supportiveAutisticState
    ≡ diagnosticProjection highDemandAutisticState
sameAcceptedDiagnosticCategory = refl

situatedResponsesDiffer :
  situatedResponse supportiveAutisticState
    ≡ situatedResponse highDemandAutisticState → ⊥
situatedResponsesDiffer ()

diagnosticAxisNotExhaustiveForSituatedResponse :
  Intersection.NonFactorabilityWitness diagnosticProjection situatedResponse
diagnosticAxisNotExhaustiveForSituatedResponse =
  Intersection.nonFactorabilityWitness
    supportiveAutisticState
    highDemandAutisticState
    sameAcceptedDiagnosticCategory
    situatedResponsesDiffer

diagnosticReweightingCannotRecoverSituatedResponse :
  Intersection.FactorsThrough diagnosticProjection situatedResponse → ⊥
diagnosticReweightingCannotRecoverSituatedResponse =
  Intersection.witnessRulesOutEveryFlatFactorisation
    diagnosticAxisNotExhaustiveForSituatedResponse

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record PositiveAutismLandscapeBoundary : Set where
  constructor positiveAutismLandscapeBoundary
  field
    diagnosticCategoryRetainedAsResearchCoordinate : Bool
    diagnosticCategoryRetainedAsResearchCoordinateIsTrue :
      diagnosticCategoryRetainedAsResearchCoordinate ≡ true

    staticConnectomeIsOnlyPossibleDistinguishingFactor : Bool
    staticConnectomeIsOnlyPossibleDistinguishingFactorIsFalse :
      staticConnectomeIsOnlyPossibleDistinguishingFactor ≡ false

    memoryLearningProcessingCanBeTypedSeparately : Bool
    memoryLearningProcessingCanBeTypedSeparatelyIsTrue :
      memoryLearningProcessingCanBeTypedSeparately ≡ true

    intersectionalContextIsMerelyAnAdditiveAfterthought : Bool
    intersectionalContextIsMerelyAnAdditiveAfterthoughtIsFalse :
      intersectionalContextIsMerelyAnAdditiveAfterthought ≡ false

    citedLiteratureProvesOneUniversalAutisticTransitionLaw : Bool
    citedLiteratureProvesOneUniversalAutisticTransitionLawIsFalse :
      citedLiteratureProvesOneUniversalAutisticTransitionLaw ≡ false

    syntheticFiniteDynamicsAreEmpiricalEffectSizes : Bool
    syntheticFiniteDynamicsAreEmpiricalEffectSizesIsFalse :
      syntheticFiniteDynamicsAreEmpiricalEffectSizes ≡ false

canonicalPositiveAutismLandscapeBoundary : PositiveAutismLandscapeBoundary
canonicalPositiveAutismLandscapeBoundary =
  positiveAutismLandscapeBoundary
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl

module DASHI.Law.SensibLawPrecedentGeometryStatisticsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- STRUCTURED PRECEDENT GEOMETRY
------------------------------------------------------------------------

record StructuredCase : Set₁ where
  constructor structuredCase
  field
    caseReference : String
    factsReference : String
    issuesReference : String
    rulesReference : String
    argumentsReference : String
    holdingsReference : String
    ordersReference : String
    citationsReference : String
    treatmentReference : String
    outcomeReference : String
    judgeReference : String
    temporalReference : String
    jurisdictionReference : String
    courtHierarchyReference : String
    structureReviewReceipt : Set

open StructuredCase public

record CaseFibreComparison : Set₁ where
  constructor caseFibreComparison
  field
    leftCase : StructuredCase
    rightCase : StructuredCase
    sharedCoordinatesReference : String
    differingCoordinatesReference : String
    issueIdentityReceipt : Set
    comparisonReference : String

open CaseFibreComparison public

record MinimalSeparatorCandidate : Set₁ where
  constructor minimalSeparatorCandidate
  field
    comparison : CaseFibreComparison
    separatingCoordinateReference : String
    leftOutcomeReference : String
    rightOutcomeReference : String
    minimalityEvidenceReference : String
    doctrinalStatusUnresolvedReceipt : Set
    separatorReference : String

open MinimalSeparatorCandidate public

------------------------------------------------------------------------
-- Counterfactual/nearest-comparator search remains candidate generation.
------------------------------------------------------------------------

record NearestOutcomeComparator : Set₁ where
  constructor nearestOutcomeComparator
  field
    targetCase : StructuredCase
    comparatorCase : StructuredCase
    sharedFibreReference : String
    outcomeDifferenceReference : String
    deltaReference : String
    comparatorDistanceReference : String
    candidateDiscriminatorReference : String
    comparisonReference : String

open NearestOutcomeComparator public

------------------------------------------------------------------------
-- Descriptive jurisprudential statistics.
------------------------------------------------------------------------

data StatisticKind : Set where
  propositionAdoptionStatistic
  argumentOutcomeStatistic
  doctrinalTransitionStatistic
  lexicalRealisationStatistic
  authorityTreatmentStatistic
  separatorFrequencyStatistic
  : StatisticKind

record DescriptiveLegalStatistic : Set₁ where
  constructor descriptiveLegalStatistic
  field
    statisticKind : StatisticKind
    sampleUniverseReference : String
    sampleCount : Nat
    targetReference : String
    conditioningAxesReference : String
    resultReference : String
    methodologyReference : String
    provenanceReference : String
    descriptiveOnly : Bool
    descriptiveOnlyIsTrue : descriptiveOnly ≡ true

open DescriptiveLegalStatistic public

------------------------------------------------------------------------
-- Corpus-derived lexical fibres for better provider queries.
------------------------------------------------------------------------

record JudicialLexicalRealisation : Set where
  constructor judicialLexicalRealisation
  field
    semanticConceptReference : String
    lexicalSurface : String
    jurisdictionReference : String
    courtReference : String
    temporalEnvelopeReference : String
    observationCount : Nat
    lexicalReference : String

open JudicialLexicalRealisation public

record LexicalFibre : Set₁ where
  constructor lexicalFibre
  field
    conceptReference : String
    realisations : List JudicialLexicalRealisation
    corpusSliceReference : String
    fibreReference : String

open LexicalFibre public

------------------------------------------------------------------------
-- Doctrinal-transition topology.
------------------------------------------------------------------------

data DoctrinalTransitionKind : Set where
  ruleToException
  exceptionToDistinction
  distinctionToNewRule
  authorityTreatmentShift
  lexicalShiftWithoutDoctrinalProof
  : DoctrinalTransitionKind

record DoctrinalTransitionCandidate : Set where
  constructor doctrinalTransitionCandidate
  field
    fromStateReference : String
    toStateReference : String
    transitionKind : DoctrinalTransitionKind
    temporalReference : String
    authoritySequenceReference : String
    transitionCandidateOnly : Bool
    transitionCandidateOnlyIsTrue : transitionCandidateOnly ≡ true
    transitionReference : String

open DoctrinalTransitionCandidate public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CorrelationAutomaticallyDoctrine : Set where
data OutcomeSeparatorAutomaticallyCausal : Set where
data NearestComparatorAutomaticallyControllingPrecedent : Set where
data FrequentArgumentAutomaticallyLegallyValid : Set where
data LexicalFrequencyAutomaticallySemanticMeaning : Set where
data DescriptiveStatisticAutomaticallyAuthority : Set where

correlationDoesNotBecomeDoctrine : CorrelationAutomaticallyDoctrine → ⊥
correlationDoesNotBecomeDoctrine ()

separatorDoesNotBecomeCausal : OutcomeSeparatorAutomaticallyCausal → ⊥
separatorDoesNotBecomeCausal ()

nearestComparatorDoesNotBecomeControllingPrecedent :
  NearestComparatorAutomaticallyControllingPrecedent → ⊥
nearestComparatorDoesNotBecomeControllingPrecedent ()

frequencyDoesNotBecomeValidity : FrequentArgumentAutomaticallyLegallyValid → ⊥
frequencyDoesNotBecomeValidity ()

lexicalFrequencyDoesNotFixMeaning : LexicalFrequencyAutomaticallySemanticMeaning → ⊥
lexicalFrequencyDoesNotFixMeaning ()

statisticDoesNotBecomeAuthority : DescriptiveStatisticAutomaticallyAuthority → ⊥
statisticDoesNotBecomeAuthority ()

record PrecedentGeometryBoundary : Set where
  constructor precedentGeometryBoundary
  field
    structuredCasesEnableFibreComparison : Bool
    structuredCasesEnableFibreComparisonIsTrue :
      structuredCasesEnableFibreComparison ≡ true
    minimalSeparatorsAreSearchTargets : Bool
    minimalSeparatorsAreSearchTargetsIsTrue : minimalSeparatorsAreSearchTargets ≡ true
    descriptiveStatisticsMayGuideSearch : Bool
    descriptiveStatisticsMayGuideSearchIsTrue : descriptiveStatisticsMayGuideSearch ≡ true
    statisticsBecomeDoctrineAutomatically : Bool
    statisticsBecomeDoctrineAutomaticallyIsFalse : statisticsBecomeDoctrineAutomatically ≡ false
    nearestOutcomeComparatorProvesCausation : Bool
    nearestOutcomeComparatorProvesCausationIsFalse : nearestOutcomeComparatorProvesCausation ≡ false

canonicalPrecedentGeometryBoundary : PrecedentGeometryBoundary
canonicalPrecedentGeometryBoundary =
  precedentGeometryBoundary true refl true refl true refl false refl false refl

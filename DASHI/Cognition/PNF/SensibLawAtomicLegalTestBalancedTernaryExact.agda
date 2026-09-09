module DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule

------------------------------------------------------------------------
-- ATOMIC BALANCED-TERNARY LEGAL TEST
--
-- Two source roles are independent:
--   * sourceReceipt defines/owns the legal test proposition itself;
--   * outcome evidence explains why this case fits or fails that exact test.
--
-- A case disposition can therefore establish failure of a test without
-- silently becoming the source that defines the general legal test.
------------------------------------------------------------------------

record AtomicOutcomeSource
    (testProposition : Algebra.LegalProposition) : Set₁ where
  constructor atomic-outcome-source
  field
    evidenceProposition : Algebra.LegalProposition
    evidenceSource : SourceRule.PropositionSourceReceipt evidenceProposition
    testAtom : Ontology.StableId
    testAtomIsExact : testAtom ≡ Algebra.propositionId testProposition
    evidenceSystemMatchesTest :
      Algebra.legalSystem evidenceProposition
      ≡ Algebra.legalSystem testProposition
    evidenceRelation : String

open AtomicOutcomeSource public

record SourceConditionedAtomicLegalTest
    (p : Algebra.LegalProposition) : Set₁ where
  constructor source-conditioned-atomic-legal-test
  field
    -- Source that defines/owns this exact legal test.
    sourceReceipt : SourceRule.PropositionSourceReceipt p

    subject : Ontology.StableId
    subjectMatchesProposition : subject ≡ Algebra.subjectReference p

    Fits : Set
    FailsToFit : Set
    fitAndFailureExclusive : Fits → FailsToFit → ⊥

    -- Every concrete fit/failure witness retains independently attributed
    -- outcome evidence.  In particular `neg` is a positive sourced failure
    -- witness, not the logical opposite of p.
    fitOutcomeSource : Fits → AtomicOutcomeSource p
    failureOutcomeSource : FailsToFit → AtomicOutcomeSource p

    gate : BT.Trit
    positiveGateHasFitWitness : gate ≡ BT.pos → Fits
    negativeGateHasFailureWitness : gate ≡ BT.neg → FailsToFit

    testReference : String

open SourceConditionedAtomicLegalTest public

positiveWitness :
  ∀ {p} (test : SourceConditionedAtomicLegalTest p) →
  gate test ≡ BT.pos → Fits test
positiveWitness test = positiveGateHasFitWitness test

negativeFailureWitness :
  ∀ {p} (test : SourceConditionedAtomicLegalTest p) →
  gate test ≡ BT.neg → FailsToFit test
negativeFailureWitness test = negativeGateHasFailureWitness test

positiveOutcomeEvidence :
  ∀ {p} (test : SourceConditionedAtomicLegalTest p) →
  Fits test → AtomicOutcomeSource p
positiveOutcomeEvidence test = fitOutcomeSource test

negativeOutcomeEvidence :
  ∀ {p} (test : SourceConditionedAtomicLegalTest p) →
  FailsToFit test → AtomicOutcomeSource p
negativeOutcomeEvidence test = failureOutcomeSource test

positiveAndNegativeWitnessesConflict :
  ∀ {p} (test : SourceConditionedAtomicLegalTest p) →
  Fits test → FailsToFit test → ⊥
positiveAndNegativeWitnessesConflict test = fitAndFailureExclusive test

------------------------------------------------------------------------
-- Atomicity / attribution firewalls.
------------------------------------------------------------------------

data NegativeGateProvesOppositeProposition : Set where
data UnresolvedGateCountsAsFailure : Set where
data UnresolvedGateCountsAsFit : Set where
data AtomicGateCreatesLegalAuthority : Set where
data FailureOfOneAtomProvesAnotherAtom : Set where
data AtomicTestMayFloatToDifferentSubject : Set where
data DefinitionSourceAloneDeterminesOutcome : Set where
data FailureOutcomeSourceDefinesGeneralLegalTest : Set where

negativeGateDoesNotProveOppositeProposition :
  NegativeGateProvesOppositeProposition → ⊥
negativeGateDoesNotProveOppositeProposition ()

unresolvedDoesNotCountAsFailure : UnresolvedGateCountsAsFailure → ⊥
unresolvedDoesNotCountAsFailure ()

unresolvedDoesNotCountAsFit : UnresolvedGateCountsAsFit → ⊥
unresolvedDoesNotCountAsFit ()

atomicGateDoesNotCreateAuthority : AtomicGateCreatesLegalAuthority → ⊥
atomicGateDoesNotCreateAuthority ()

failureOfOneAtomDoesNotProveAnother : FailureOfOneAtomProvesAnotherAtom → ⊥
failureOfOneAtomDoesNotProveAnother ()

atomicTestCannotFloatToDifferentSubject : AtomicTestMayFloatToDifferentSubject → ⊥
atomicTestCannotFloatToDifferentSubject ()

definitionSourceDoesNotDetermineCaseOutcome :
  DefinitionSourceAloneDeterminesOutcome → ⊥
definitionSourceDoesNotDetermineCaseOutcome ()

caseFailureDoesNotDefineGeneralTest :
  FailureOutcomeSourceDefinesGeneralLegalTest → ⊥
caseFailureDoesNotDefineGeneralTest ()

------------------------------------------------------------------------
-- Example requested by the corruption / business-practice axis.
------------------------------------------------------------------------

validBusinessPracticeAxis : Ontology.StableId
validBusinessPracticeAxis = Ontology.stableId "axis:valid-business-practice"

corruptionAxis : Ontology.StableId
corruptionAxis = Ontology.stableId "axis:corruption"

data ValidBusinessPracticeFailureIsCorruptionProof : Set where

validBusinessPracticeFailureDoesNotBecomeCorruptionProof :
  ValidBusinessPracticeFailureIsCorruptionProof → ⊥
validBusinessPracticeFailureDoesNotBecomeCorruptionProof ()

record AtomicLegalTestBoundary : Set where
  constructor atomic-legal-test-boundary
  field
    positiveMeansFitWitness : Bool
    zeroMeansUnresolved : Bool
    negativeMeansFailureWitnessForSameAtom : Bool
    negativeMeansLogicalOpposite : Bool
    unresolvedPromotesEitherDirection : Bool
    sourceConditioningRequired : Bool
    exactSubjectWeldRequired : Bool
    testDefinitionSourceSeparatedFromOutcomeSource : Bool
    negativeOutcomeRequiresPositiveSourcedFailureEvidence : Bool

canonicalAtomicLegalTestBoundary : AtomicLegalTestBoundary
canonicalAtomicLegalTestBoundary =
  atomic-legal-test-boundary
    true true true false false true true true true

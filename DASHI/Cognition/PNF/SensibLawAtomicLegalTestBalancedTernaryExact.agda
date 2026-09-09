module DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule

record SourceConditionedAtomicLegalTest
    (p : Algebra.LegalProposition) : Set₁ where
  constructor source-conditioned-atomic-legal-test
  field
    sourceReceipt : SourceRule.PropositionSourceReceipt p
    subject : Ontology.StableId
    subjectMatchesProposition : subject ≡ Algebra.subjectReference p
    Fits : Set
    FailsToFit : Set
    fitAndFailureExclusive : Fits → FailsToFit → ⊥
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

positiveAndNegativeWitnessesConflict :
  ∀ {p} (test : SourceConditionedAtomicLegalTest p) →
  Fits test → FailsToFit test → ⊥
positiveAndNegativeWitnessesConflict test = fitAndFailureExclusive test

data NegativeGateProvesOppositeProposition : Set where
data UnresolvedGateCountsAsFailure : Set where
data UnresolvedGateCountsAsFit : Set where
data AtomicGateCreatesLegalAuthority : Set where
data FailureOfOneAtomProvesAnotherAtom : Set where
data AtomicTestMayFloatToDifferentSubject : Set where

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

canonicalAtomicLegalTestBoundary : AtomicLegalTestBoundary
canonicalAtomicLegalTestBoundary =
  atomic-legal-test-boundary true true true false false true true

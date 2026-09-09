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
-- The trit is an admissibility / sufficiency / fit coordinate for ONE atomic
-- legal test.  It is not a three-valued truth semantics and `neg` is not the
-- logical or lexical opposite of the proposition.
--
--   pos  = positive witness that this atom fits / passes
--   zero = the atom remains unresolved on the present evidence fibre
--   neg  = positive witness that this atom fails to fit / pass
--
-- Thus, for example, failure of an atom `validBusinessPractice` does not by
-- itself establish a different proposition `corruption`.  Such an implication
-- requires its own sourced legal rule.
------------------------------------------------------------------------

record SourceConditionedAtomicLegalTest
    (p : Algebra.LegalProposition) : Set₁ where
  constructor source-conditioned-atomic-legal-test
  field
    sourceReceipt : SourceRule.PropositionSourceReceipt p
    subject : Ontology.StableId

    Fits : Set
    FailsToFit : Set
    fitAndFailureExclusive : Fits → FailsToFit → ⊥

    gate : BT.Trit
    positiveGateHasFitWitness : gate ≡ BT.pos → Fits
    negativeGateHasFailureWitness : gate ≡ BT.neg → FailsToFit

    testReference : String

open SourceConditionedAtomicLegalTest public

------------------------------------------------------------------------
-- Gate-specific witness projections.  `zero` deliberately has no constructor
-- that manufactures either a fit or a failure witness.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Atomicity boundary: a negative gate stays indexed to the same proposition.
-- There is no generic operation that manufactures an opposite proposition.
------------------------------------------------------------------------

data NegativeGateProvesOppositeProposition : Set where
data UnresolvedGateCountsAsFailure : Set where
data UnresolvedGateCountsAsFit : Set where
data AtomicGateCreatesLegalAuthority : Set where
data FailureOfOneAtomProvesAnotherAtom : Set where

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

------------------------------------------------------------------------
-- Example shape only: failure of the valid-business-practice atom remains a
-- failure witness for that axis.  No corruption proposition is produced here.
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

canonicalAtomicLegalTestBoundary : AtomicLegalTestBoundary
canonicalAtomicLegalTestBoundary =
  atomic-legal-test-boundary true true true false false true

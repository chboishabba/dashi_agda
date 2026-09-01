module DASHI.Reasoning.SpacyNegationCounterpositionTernarySeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Spacy
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank
import DASHI.Reasoning.DialecticalOppositionNonExplosionExact as Opposition
import DASHI.Reasoning.SpacyPNF369DialecticBridgeExact as Bridge369

------------------------------------------------------------------------
-- SPACY NEGATION != DIALECTICAL COUNTERPOSITION != TERNARY SUSPENSION
--
-- A dependency `neg` edge may license a candidate logical `notF` formula only
-- after shape admission.  Contextual counterposition remains a separately
-- constructed operation, while tri-mid records suspension/refinement policy.
------------------------------------------------------------------------

record AdmittedSpacyNegation : Set₁ where
  constructor admittedSpacyNegation
  field
    witness : Spacy.DependencyWitness
    admission : RuleBank.ShapeAdmission witness Spacy.negation
    body : Spacy.Formula
    candidate : Spacy.CandidateSemanticFragment
    candidateExact :
      candidate ≡ RuleBank.negationScopeRule witness admission body
    scopeReviewReference : String

open AdmittedSpacyNegation public

negationCandidateFormulaIsNotF :
  (neg : AdmittedSpacyNegation) →
  Spacy.formula (candidate neg)
  ≡ Spacy.notF (body neg)
negationCandidateFormulaIsNotF
  (admittedSpacyNegation witness admission body .(RuleBank.negationScopeRule witness admission body) refl ref) = refl

------------------------------------------------------------------------
-- Operator tags prevent accidental identification even when prose says
-- "opposite" in all three cases.
------------------------------------------------------------------------

data SpacyDialecticOperator : Set where
  parserScopedNegation
  contextualCounterposition
  ternarySuspension
  : SpacyDialecticOperator

parserNegationIsNotCounterposition :
  parserScopedNegation ≡ contextualCounterposition → ⊥
parserNegationIsNotCounterposition ()

parserNegationIsNotSuspension :
  parserScopedNegation ≡ ternarySuspension → ⊥
parserNegationIsNotSuspension ()

counterpositionIsNotSuspension :
  contextualCounterposition ≡ ternarySuspension → ⊥
counterpositionIsNotSuspension ()

repositoryCounterpositionStillNotLogicalNegation :
  Opposition.constructedCounterposition ≡ Opposition.logicalNegation → ⊥
repositoryCounterpositionStillNotLogicalNegation = Opposition.counterposition≢negation

------------------------------------------------------------------------
-- Ternary suspension is the review/control coordinate, not a new formula
-- connective.  In particular it does not turn `phi` into `notF phi`.
------------------------------------------------------------------------

suspensionMapsToNeutral :
  Bridge369.dispositionTrit Bridge369.suspendCandidate ≡ Base.tri-mid
suspensionMapsToNeutral = refl

rejectMapsToLow :
  Bridge369.dispositionTrit Bridge369.rejectCandidate ≡ Base.tri-low
rejectMapsToLow = refl

admitMapsToHigh :
  Bridge369.dispositionTrit Bridge369.admitCandidate ≡ Base.tri-high
admitMapsToHigh = refl

suspensionIsNotReject :
  Bridge369.dispositionTrit Bridge369.suspendCandidate
  ≡ Bridge369.dispositionTrit Bridge369.rejectCandidate → ⊥
suspensionIsNotReject ()

suspensionIsNotAdmit :
  Bridge369.dispositionTrit Bridge369.suspendCandidate
  ≡ Bridge369.dispositionTrit Bridge369.admitCandidate → ⊥
suspensionIsNotAdmit ()

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record SpacyNegationDialecticBoundary : Set where
  constructor spacyNegationDialecticBoundary
  field
    admittedNegEdgeMayProposeNotF : Bool
    admittedNegEdgeMayProposeNotFIsTrue : admittedNegEdgeMayProposeNotF ≡ true
    negEdgeFixesFinalSemanticScope : Bool
    negEdgeFixesFinalSemanticScopeIsFalse : negEdgeFixesFinalSemanticScope ≡ false
    parserNegationIsCounterposition : Bool
    parserNegationIsCounterpositionIsFalse : parserNegationIsCounterposition ≡ false
    parserNegationIsTernarySuspension : Bool
    parserNegationIsTernarySuspensionIsFalse : parserNegationIsTernarySuspension ≡ false
    ternarySuspensionIsLogicalFalsehood : Bool
    ternarySuspensionIsLogicalFalsehoodIsFalse : ternarySuspensionIsLogicalFalsehood ≡ false
    unresolvedOppositionCreatesContradiction : Bool
    unresolvedOppositionCreatesContradictionIsFalse : unresolvedOppositionCreatesContradiction ≡ false

canonicalSpacyNegationDialecticBoundary : SpacyNegationDialecticBoundary
canonicalSpacyNegationDialecticBoundary =
  spacyNegationDialecticBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

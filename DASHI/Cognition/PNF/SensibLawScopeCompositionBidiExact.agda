module DASHI.Cognition.PNF.SensibLawScopeCompositionBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank

------------------------------------------------------------------------
-- BIDI CAMPAIGN 4: modality, negation, condition and temporal scope.
--
-- Scope is a joint composition object.  Individual parser edges may propose
-- qualifications, but occurrence/truth status may only be refined against the
-- combined scope receipt.  The exact proposition/event references are retained.
------------------------------------------------------------------------

record ScopeCompositionReceipt : Set where
  constructor scopeCompositionReceipt
  field
    proposition : Status.PropositionStatusProduct
    event : Status.EventStatusProduct
    body : Candidate.Formula
    dependencyWitnesses : List Candidate.DependencyWitness
    modalityKind : Status.ModalityKind
    modalForce : Status.ModalForce
    modalScope : Status.ScopeStatus
    negationScope : Status.ScopeStatus
    conditionKind : Status.ConditionKind
    conditionScope : Status.ScopeStatus
    temporalRelation : Status.TemporalRelationKind
    temporalScope : Status.ScopeStatus
    compositionReference : String
    parserOnlyInputs : Bool
    regexSemanticInputs : Bool

open ScopeCompositionReceipt public

record ScopeQualifiedOccurrence : Set where
  constructor scopeQualifiedOccurrence
  field
    source : ScopeCompositionReceipt
    resultingOccurrence : Status.OccurrenceStatus
    resultingPropositionStatus : Status.PropositionStatus
    resultingTruth : Status.TruthStatus
    sameEventReference :
      Status.eventReference (event source)
      ≡ Status.eventReference (event source)
    samePropositionReference :
      Status.propositionReference (proposition source)
      ≡ Status.propositionReference (proposition source)

open ScopeQualifiedOccurrence public

preserveReferenceScopeQualification :
  ScopeCompositionReceipt →
  Status.OccurrenceStatus →
  Status.PropositionStatus →
  Status.TruthStatus →
  ScopeQualifiedOccurrence
preserveReferenceScopeQualification source occurrence propositionStatus truth =
  scopeQualifiedOccurrence source occurrence propositionStatus truth refl refl

------------------------------------------------------------------------
-- Existing rule-bank boundaries are consumed rather than duplicated.
------------------------------------------------------------------------

modalEdgeAloneStillNoTheorem :
  RuleBank.modalAuxiliaryCreatesModalTheorem
    RuleBank.canonicalExecutableSemanticRuleBoundary ≡ false
modalEdgeAloneStillNoTheorem = refl

conditionalStillRequiresCompositeEvidence :
  RuleBank.conditionalMayRequireCompositeEvidence
    RuleBank.canonicalExecutableSemanticRuleBoundary ≡ true
conditionalStillRequiresCompositeEvidence = refl

relativeClauseStillRequiresCompositeEvidence :
  RuleBank.relativeClauseMayRequireCompositeEvidence
    RuleBank.canonicalExecutableSemanticRuleBoundary ≡ true
relativeClauseStillRequiresCompositeEvidence = refl

------------------------------------------------------------------------
-- Consumer-safe projections.  A consumer may ask for one axis while the other
-- axes remain available in the source receipt.
------------------------------------------------------------------------

modalityProjection : ScopeCompositionReceipt → Status.ModalityKind
modalityProjection = modalityKind

conditionProjection : ScopeCompositionReceipt → Status.ConditionKind
conditionProjection = conditionKind

temporalProjection : ScopeCompositionReceipt → Status.TemporalRelationKind
temporalProjection = temporalRelation

------------------------------------------------------------------------
-- Hard no-go laws.
------------------------------------------------------------------------

data NegationEdgeFixesWholePropositionScope : Set where
data ModalSurfaceFixesDeonticForce : Set where
data ConditionalMarkerProvesAntecedentBoundary : Set where
data TemporalModifierProvesEventOccurrence : Set where
data ScopeResolutionProvesTruth : Set where
data RegexMayResolveScope : Set where

negationEdgeDoesNotFixWholeScope : NegationEdgeFixesWholePropositionScope → ⊥
negationEdgeDoesNotFixWholeScope ()

modalSurfaceDoesNotFixForce : ModalSurfaceFixesDeonticForce → ⊥
modalSurfaceDoesNotFixForce ()

conditionalMarkerDoesNotProveBoundary : ConditionalMarkerProvesAntecedentBoundary → ⊥
conditionalMarkerDoesNotProveBoundary ()

temporalModifierDoesNotProveOccurrence : TemporalModifierProvesEventOccurrence → ⊥
temporalModifierDoesNotProveOccurrence ()

scopeResolutionDoesNotProveTruth : ScopeResolutionProvesTruth → ⊥
scopeResolutionDoesNotProveTruth ()

regexCannotResolveSemanticScope : RegexMayResolveScope → ⊥
regexCannotResolveSemanticScope ()

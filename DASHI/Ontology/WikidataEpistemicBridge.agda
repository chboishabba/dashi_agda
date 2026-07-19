module DASHI.Ontology.WikidataEpistemicBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.ContextualClaimComposition

------------------------------------------------------------------------
-- A deliberately small adapter surface for Wikidata-like statements.
--
-- This does not redefine Wikidata's data model or claim that statement rank is
-- a truth value.  It records the pieces needed by an epistemic interpretation:
-- statement identity, qualifiers/context, references, and rank metadata.

data StatementRank : Set where
  preferred normal deprecated : StatementRank

record StatementEnvelope (QualifierAxis : Set) : Set where
  constructor statementEnvelope
  field
    statementId : String
    qualifierState : QualifierAxis → EpistemicTrit
    sourceReferences : List String
    rankMetadata : StatementRank

open StatementEnvelope public

asScopedClaim :
  ∀ {QualifierAxis : Set} →
  StatementEnvelope QualifierAxis →
  ScopedClaim QualifierAxis
asScopedClaim statement =
  scopedClaim
    (qualifierState statement)
    (sourceReferences statement)

adapterPreservesState :
  ∀ {QualifierAxis : Set}
    (statement : StatementEnvelope QualifierAxis)
    (axis : QualifierAxis) →
  stateAt (asScopedClaim statement) axis ≡ qualifierState statement axis
adapterPreservesState statement axis = refl

adapterPreservesReferences :
  ∀ {QualifierAxis : Set}
    (statement : StatementEnvelope QualifierAxis) →
  references (asScopedClaim statement) ≡ sourceReferences statement
adapterPreservesReferences statement = refl

------------------------------------------------------------------------
-- Rank remains metadata.  No theorem silently promotes preferred/normal/
-- deprecated into supported/unresolved/contradicted.

rankIsTruthValue : Bool
rankIsTruthValue = false

rankIsTruthValueIsFalse : rankIsTruthValue ≡ false
rankIsTruthValueIsFalse = refl

------------------------------------------------------------------------
-- Confidence is attached to the complete assessment, not used as a replacement
-- for the three epistemic states.  Nat is an abstract score carrier here; a
-- downstream calibration layer may interpret or bound it.

record ResponseAssessment (Clause : Set) : Set where
  constructor responseAssessment
  field
    clauseState : Clause → EpistemicTrit
    responseConfidence : Nat

open ResponseAssessment public

confidenceDoesNotRewriteClauseState :
  ∀ {Clause : Set}
    (states : Clause → EpistemicTrit)
    (confidence : Nat)
    (clause : Clause) →
  clauseState (responseAssessment states confidence) clause ≡ states clause
confidenceDoesNotRewriteClauseState states confidence clause = refl

------------------------------------------------------------------------
-- Deterministic evidence composition used by the DASHI/SensibLaw adapter.
-- Temperature/sampling is intentionally outside this theorem surface.

composeStatements :
  ∀ {QualifierAxis : Set} →
  StatementEnvelope QualifierAxis →
  StatementEnvelope QualifierAxis →
  ScopedClaim QualifierAxis
composeStatements left right =
  asScopedClaim left ⊗ᶜ asScopedClaim right

composedStatementState :
  ∀ {QualifierAxis : Set}
    (left right : StatementEnvelope QualifierAxis)
    (axis : QualifierAxis) →
  stateAt (composeStatements left right) axis
  ≡ qualifierState left axis ⊗ₑ qualifierState right axis
composedStatementState left right axis = refl

conflictingStatementsRemainUnresolved :
  ∀ {QualifierAxis : Set}
    (left right : StatementEnvelope QualifierAxis)
    (axis : QualifierAxis) →
  qualifierState left axis ≡ supported →
  qualifierState right axis ≡ contradicted →
  stateAt (composeStatements left right) axis ≡ unresolved
conflictingStatementsRemainUnresolved left right axis refl refl = refl

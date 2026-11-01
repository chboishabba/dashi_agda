module DASHI.Interop.SensibLawSemanticPromotionPolicyRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.TetralemmaBridge using
  ( affirmation
  ; negation
  ; both
  ; neither
  )
open import DASHI.Interop.SensibLawSemanticPromotionPolicy

------------------------------------------------------------------------
-- Canonical policy witnesses.

structuralAffirmationCandidate : SemanticCandidate
structuralAffirmationCandidate =
  structuralCandidate
    true false
    "predicate_text"
    "dependency-backed response binding"

structuralNegationCandidate : SemanticCandidate
structuralNegationCandidate =
  structuralCandidate
    false true
    "predicate_text"
    "dependency-backed negation binding"

structuralConflictCandidate : SemanticCandidate
structuralConflictCandidate =
  structuralCandidate
    true true
    "predicate_text"
    "two structurally grounded contested spans"

structuralAbstentionCandidate : SemanticCandidate
structuralAbstentionCandidate =
  structuralCandidate
    false false
    "predicate_text"
    "no structurally licensed relation"

lexicalCueOnlyCandidate : SemanticCandidate
lexicalCueOnlyCandidate =
  heuristicCandidate
    true false
    "justification_hint"
    "surface-form cue retained for review only"

mixedCueCandidate : SemanticCandidate
mixedCueCandidate =
  mixedCandidate
    false true
    true false
    "predicate_text"
    "structural negation plus contrary lexical hint"

------------------------------------------------------------------------
-- Regression equalities.

structural-affirmation-regression :
  promote structuralAffirmationCandidate ≡ affirmation
structural-affirmation-regression = refl

structural-negation-regression :
  promote structuralNegationCandidate ≡ negation
structural-negation-regression = refl

structural-conflict-regression :
  promote structuralConflictCandidate ≡ both
structural-conflict-regression = refl

structural-abstention-regression :
  promote structuralAbstentionCandidate ≡ neither
structural-abstention-regression = refl

lexical-cue-cannot-promote-regression :
  promote lexicalCueOnlyCandidate ≡ neither
lexical-cue-cannot-promote-regression = refl

mixed-cue-does-not-override-structure-regression :
  promote mixedCueCandidate ≡ negation
mixed-cue-does-not-override-structure-regression = refl

mixed-cue-invariance-regression :
  promote
    (mixedCandidate
      false true
      true false
      "predicate_text"
      "candidate A")
  ≡
  promote
    (mixedCandidate
      false true
      false true
      "predicate_text"
      "candidate B")
mixed-cue-invariance-regression = refl

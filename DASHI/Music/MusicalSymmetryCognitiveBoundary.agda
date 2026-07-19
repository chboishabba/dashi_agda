module DASHI.Music.MusicalSymmetryCognitiveBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Structural closure and cognitive-promotion boundary.
--
-- The exact finite witness closes a dynamical extension of algebraic symmetry.
-- It does not, by itself, explain human preference, perception, memory, or
-- musical cognition.  Those claims require a mechanism not equivalent to an
-- explicit symmetry reward, null-model defeat, held-out replication, and
-- behavioural evidence.
------------------------------------------------------------------------

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true ∧ right = right
false ∧ _ = false

record DynamicalExtensionGate : Set where
  constructor dynamicalExtensionGate
  field
    involutiveSymmetrySpecified : Bool
    zeroDefectFixedClassProved : Bool
    repairFixedPointEquivalenceProved : Bool
    finiteBasinPartitionComputed : Bool

  structuralClosed : Bool
  structuralClosed =
    involutiveSymmetrySpecified
    ∧ zeroDefectFixedClassProved
    ∧ repairFixedPointEquivalenceProved
    ∧ finiteBasinPartitionComputed

open DynamicalExtensionGate public

canonicalStructuralGate : DynamicalExtensionGate
canonicalStructuralGate =
  dynamicalExtensionGate
    true
    true
    true
    true

canonicalStructuralGateClosed :
  structuralClosed canonicalStructuralGate ≡ true
canonicalStructuralGateClosed = refl

record CognitiveExplanationGate : Set where
  constructor cognitiveExplanationGate
  field
    directSymmetryRewardAbsent : Bool
    mechanismDerivedFromIndependentPrinciple : Bool
    geometricNullModelDefeated : Bool
    shuffledPriorControlDefeated : Bool
    heldOutCorpusReplicated : Bool
    humanPerceptionCorrelationPresent : Bool
    quantisationAndRepresentationRobust : Bool

  cognitiveExplanationClosed : Bool
  cognitiveExplanationClosed =
    directSymmetryRewardAbsent
    ∧ mechanismDerivedFromIndependentPrinciple
    ∧ geometricNullModelDefeated
    ∧ shuffledPriorControlDefeated
    ∧ heldOutCorpusReplicated
    ∧ humanPerceptionCorrelationPresent
    ∧ quantisationAndRepresentationRobust

open CognitiveExplanationGate public

------------------------------------------------------------------------
-- The original beta-weighted toy is blocked because it directly rewards the
-- target asymmetry functional and has no held-out behavioural evidence.
------------------------------------------------------------------------

betaWeightedToyGate : CognitiveExplanationGate
betaWeightedToyGate =
  cognitiveExplanationGate
    false
    false
    false
    false
    false
    false
    false

betaWeightedToyCognitiveClaimBlocked :
  cognitiveExplanationClosed betaWeightedToyGate ≡ false
betaWeightedToyCognitiveClaimBlocked = refl

------------------------------------------------------------------------
-- The replacement MDL diagnostic removes direct E_sym reward and introduces
-- null controls.  It remains candidate-only until the remaining empirical and
-- robustness gates are discharged.
------------------------------------------------------------------------

mdlCompressionCandidateGate : CognitiveExplanationGate
mdlCompressionCandidateGate =
  cognitiveExplanationGate
    true
    true
    false
    false
    false
    false
    false

mdlCompressionCognitiveClaimStillBlocked :
  cognitiveExplanationClosed mdlCompressionCandidateGate ≡ false
mdlCompressionCognitiveClaimStillBlocked = refl

musicalSymmetryCognitiveExplanationPromoted : Bool
musicalSymmetryCognitiveExplanationPromoted = false

musicalSymmetryCognitiveExplanationPromotedIsFalse :
  musicalSymmetryCognitiveExplanationPromoted ≡ false
musicalSymmetryCognitiveExplanationPromotedIsFalse = refl

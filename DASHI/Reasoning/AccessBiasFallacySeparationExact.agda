module DASHI.Reasoning.AccessBiasFallacySeparationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy

------------------------------------------------------------------------
-- Access/retrieval bias is a candidate-generation phenomenon.  A fallacy is a
-- typed obstruction in an assembled argument.  Neither determines the other.
------------------------------------------------------------------------

data AccessBias : Set where
  confirmationAccessBias : AccessBias
  threatAccessBias : AccessBias
  familiarityAccessBias : AccessBias

missingSupportNotEquivocation :
  Fallacy.missingPremiseSupport ≡ Fallacy.semanticEquivocation → ⊥
missingSupportNotEquivocation ()

threatNotFamiliarity : threatAccessBias ≡ familiarityAccessBias → ⊥
threatNotFamiliarity ()

------------------------------------------------------------------------
-- Same access bias, different formal obstruction: no bias-only decoder can be
-- forced to explain both argument outcomes.
------------------------------------------------------------------------

sameBiasCanFeedDifferentFallacies :
  (decode : AccessBias → Fallacy.FallacyObstruction) →
  decode confirmationAccessBias ≡ Fallacy.missingPremiseSupport →
  decode confirmationAccessBias ≡ Fallacy.semanticEquivocation →
  ⊥
sameBiasCanFeedDifferentFallacies decode first second =
  missingSupportNotEquivocation (trans (sym first) second)

------------------------------------------------------------------------
-- Same fallacy, different candidate-access causes: no fallacy-only decoder can
-- recover one neural/psychological producer from argument structure alone.
------------------------------------------------------------------------

sameFallacyCanHaveDifferentAccessCauses :
  (decode : Fallacy.FallacyObstruction → AccessBias) →
  decode Fallacy.missingPremiseSupport ≡ threatAccessBias →
  decode Fallacy.missingPremiseSupport ≡ familiarityAccessBias →
  ⊥
sameFallacyCanHaveDifferentAccessCauses decode first second =
  threatNotFamiliarity (trans (sym first) second)

record CandidateGenerationBias : Set where
  constructor candidateGenerationBias
  field
    supportingCandidateAccessible : Bool
    counterCandidateAccessible : Bool

open CandidateGenerationBias public

confirmationSkew : CandidateGenerationBias
confirmationSkew = candidateGenerationBias true false

balancedAccess : CandidateGenerationBias
balancedAccess = candidateGenerationBias true true

skewAndBalancedDifferOnCounterAccess :
  counterCandidateAccessible confirmationSkew
  ≡ counterCandidateAccessible balancedAccess → ⊥
skewAndBalancedDifferOnCounterAccess ()

record AccessBiasFallacyBoundary : Set where
  constructor accessBiasFallacyBoundary
  field
    accessBiasIsDefinitionOfFallacy : Bool
    fallacyIdentifiesNeuralCause : Bool
    biasedRetrievalProvesConclusionFalse : Bool
    cleanRetrievalProvesConclusionTrue : Bool

canonicalAccessBiasFallacyBoundary : AccessBiasFallacyBoundary
canonicalAccessBiasFallacyBoundary =
  accessBiasFallacyBoundary false false false false

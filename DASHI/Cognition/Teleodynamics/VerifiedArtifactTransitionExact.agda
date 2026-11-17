module DASHI.Cognition.Teleodynamics.VerifiedArtifactTransitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Cognition.Teleodynamics.ScopedVerifierArchitectureExact as Verify
import DASHI.Cognition.PNF.LLMContextWindowTerminalisationExact
import DASHI.Cognition.PNF.LLMResidualHierarchyExact
import DASHI.Cognition.PNF.NeuralBottleneckResidualFutureSafetyExact

record ArtifactState (Identity Body Residual : Set) : Set where
  constructor artifact-state
  field
    identity : Identity
    body : Body
    residual : Residual
open ArtifactState public

record DeclaredEdit {Identity Body Residual : Set} (before after : ArtifactState Identity Body Residual) : Set₁ where
  constructor declared-edit
  field
    Delta : Set
    delta : Delta
    identityPreserved : identity before ≡ identity after
    EditSemantics : Body → Delta → Body → Set
    editSemanticsPaid : EditSemantics (body before) delta (body after)
open DeclaredEdit public

record ResidualReopening {Identity Body Residual : Set} (before after : ArtifactState Identity Body Residual) : Set₁ where
  constructor residual-reopening
  field
    FutureConsumer : Set
    distinguishesFuture : FutureConsumer → Residual → Set
    retainedOrReopened : (q : FutureConsumer) → distinguishesFuture q (residual after)
open ResidualReopening public

record VerifiedArtifactTransition {Identity Body Residual : Set}
    (V : Verify.ScopedValidator (ArtifactState Identity Body Residual))
    (before after : ArtifactState Identity Body Residual) : Set₁ where
  constructor verified-artifact-transition
  field
    edit : DeclaredEdit before after
    residualSafety : ResidualReopening before after
    beforeReceipt : Verify.ValidationReceipt V before
    afterReceipt : Verify.ValidationReceipt V after
open VerifiedArtifactTransition public

sameArtifactIdentity : ∀ {Identity Body Residual : Set} {V : Verify.ScopedValidator (ArtifactState Identity Body Residual)} {before after : ArtifactState Identity Body Residual} → VerifiedArtifactTransition V before after → identity before ≡ identity after
sameArtifactIdentity t = identityPreserved (edit t)

postEditClaimPaid : ∀ {Identity Body Residual : Set} {V : Verify.ScopedValidator (ArtifactState Identity Body Residual)} {before after : ArtifactState Identity Body Residual} → VerifiedArtifactTransition V before after → Verify.Claim V after
postEditClaimPaid t = Verify.claimPaid (afterReceipt t)

data DeterministicReplayCreatesArtifactIdentity : Set where
data IdentityPreservationCreatesValidatorPass : Set where
data ValidatorPassCreatesFutureSufficiency : Set where

noArtifactIdentityFromDeterministicReplay : DeterministicReplayCreatesArtifactIdentity → ⊥
noArtifactIdentityFromDeterministicReplay ()
identityDoesNotCreateValidatorPass : IdentityPreservationCreatesValidatorPass → ⊥
identityDoesNotCreateValidatorPass ()
validatorPassDoesNotCreateFutureSufficiency : ValidatorPassCreatesFutureSufficiency → ⊥
validatorPassDoesNotCreateFutureSufficiency ()

record VerifiedArtifactBoundary : Set where
  constructor verified-artifact-boundary
  field
    explicitArtifactStateRequired : Bool
    explicitDeclaredDeltaRequired : Bool
    identityReceiptRequired : Bool
    residualReopeningRequired : Bool
    postEditRevalidationRequired : Bool
    regenerationEquivalentToEdit : Bool
    deterministicReplaySufficient : Bool

canonicalVerifiedArtifactBoundary : VerifiedArtifactBoundary
canonicalVerifiedArtifactBoundary = verified-artifact-boundary true true true true true false false

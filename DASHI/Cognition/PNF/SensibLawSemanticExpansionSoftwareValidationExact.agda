module DASHI.Cognition.PNF.SensibLawSemanticExpansionSoftwareValidationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationExact as GWB

------------------------------------------------------------------------
-- Post-certification software-validation receipt for the richer semantic lane.
--
-- The certified GWB runtime baseline remains 60777f6... .  The semantic
-- expansion was subsequently validated at 49c09df... with workspace tests,
-- clippy -D warnings, release build and source-contract checks.  This receipt
-- records that software state without promoting it to expanded GWB parity or
-- performance certification.
------------------------------------------------------------------------

record SemanticExpansionSoftwareValidationReceipt : Set where
  constructor semanticExpansionSoftwareValidationReceipt
  field
    validatedRustHead : String
    certifiedBaselineRustHead : String
    semanticExpansionTestsPassed : Nat
    workspaceTestsPassed : Bool
    workspaceTestsPassedTrue : workspaceTestsPassed ≡ true
    clippyWarningsDeniedPassed : Bool
    clippyWarningsDeniedPassedTrue : clippyWarningsDeniedPassed ≡ true
    releaseBuildPassed : Bool
    releaseBuildPassedTrue : releaseBuildPassed ≡ true
    sourceContractsPassed : Bool
    sourceContractsPassedTrue : sourceContractsPassed ≡ true
    candidateOnlyContractChecked : Bool
    candidateOnlyContractCheckedTrue : candidateOnlyContractChecked ≡ true
    alternativeFibreRetentionChecked : Bool
    alternativeFibreRetentionCheckedTrue : alternativeFibreRetentionChecked ≡ true
    unresolvedScopeResidualsChecked : Bool
    unresolvedScopeResidualsCheckedTrue : unresolvedScopeResidualsChecked ≡ true
    noPublicationApiChecked : Bool
    noPublicationApiCheckedTrue : noPublicationApiChecked ≡ true
    worktreeClean : Bool
    worktreeCleanTrue : worktreeClean ≡ true

open SemanticExpansionSoftwareValidationReceipt public

semanticExpansionValidatedHead : String
semanticExpansionValidatedHead =
  "49c09dfffabadc909c05c0f8db27b051a0c84c01"

semanticExpansionSoftwareValidation : SemanticExpansionSoftwareValidationReceipt
semanticExpansionSoftwareValidation =
  semanticExpansionSoftwareValidationReceipt
    semanticExpansionValidatedHead
    (GWB.certifiedRustHead GWB.gwbV01Corpus)
    3
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Current post-validation frontier.
------------------------------------------------------------------------

data SemanticExpansionFrontier : Set where
  softwareValidatedAwaitingExpandedParityPerformance : SemanticExpansionFrontier

currentSemanticExpansionFrontier : SemanticExpansionFrontier
currentSemanticExpansionFrontier =
  softwareValidatedAwaitingExpandedParityPerformance

------------------------------------------------------------------------
-- Least-privilege non-promotion.
------------------------------------------------------------------------

data SoftwareValidationProvesExpandedSemanticParity : Set where

data SoftwareValidationProvesExpandedPerformanceTier : Set where

data SoftwareValidationAuthorizesPublication : Set where

data LaterValidatedHeadRetroactivelyChangesCertifiedBaseline : Set where

softwareValidationDoesNotProveExpandedParity :
  SoftwareValidationProvesExpandedSemanticParity → ⊥
softwareValidationDoesNotProveExpandedParity ()

softwareValidationDoesNotProveExpandedPerformance :
  SoftwareValidationProvesExpandedPerformanceTier → ⊥
softwareValidationDoesNotProveExpandedPerformance ()

softwareValidationDoesNotAuthorizePublication :
  SoftwareValidationAuthorizesPublication → ⊥
softwareValidationDoesNotAuthorizePublication ()

laterValidationDoesNotRewriteCertifiedBaseline :
  LaterValidatedHeadRetroactivelyChangesCertifiedBaseline → ⊥
laterValidationDoesNotRewriteCertifiedBaseline ()

------------------------------------------------------------------------
-- The old GWB receipt remains literally pinned to its own code identity.
------------------------------------------------------------------------

certifiedBaselineIdentityRemainsFrozen :
  GWB.certifiedRustHead GWB.gwbV01Corpus
  ≡ "60777f637732f28fed46458a30853d35b88a8a09"
certifiedBaselineIdentityRemainsFrozen = refl

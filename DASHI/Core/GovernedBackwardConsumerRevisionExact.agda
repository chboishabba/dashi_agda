module DASHI.Core.GovernedBackwardConsumerRevisionExact where

------------------------------------------------------------------------
-- GOVERNED BACKWARD-CONSUMER REVISION
--
-- BIDI's backward side is itself a governed object.  A producer/search route
-- must not weaken the acceptance consumer, obligation activation rule,
-- authority hierarchy, evidence criterion or residual budget while trying to
-- satisfy it.  Revision therefore carries provenance and external authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.VocabularyProvenanceExact
import DASHI.Core.ContextGovernedLineageTransportExact
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact

------------------------------------------------------------------------
-- Governed consumer state.
------------------------------------------------------------------------

data ConsumerVersion : Set where version0 version1 : ConsumerVersion
data ConsumerProvenance : Set where externallyFrozen authorisedRevision routeGeneratedRevision : ConsumerProvenance
data RevisionAuthority : Set where externalRevisionAuthority : RevisionAuthority
data RequirementStrength : Set where strongRequirement weakRequirement : RequirementStrength

record BackwardConsumer : Set where
  constructor backward-consumer
  field
    version : ConsumerVersion
    provenance : ConsumerProvenance
    strength : RequirementStrength

open BackwardConsumer public

frozenConsumer : BackwardConsumer
frozenConsumer = backward-consumer version0 externallyFrozen strongRequirement

routeWeakenedConsumer : BackwardConsumer
routeWeakenedConsumer = backward-consumer version1 routeGeneratedRevision weakRequirement

authorisedConsumerRevision : BackwardConsumer
authorisedConsumerRevision = backward-consumer version1 authorisedRevision strongRequirement

------------------------------------------------------------------------
-- Only externally authorised revision can produce a revision receipt.
------------------------------------------------------------------------

record ConsumerRevisionReceipt (source target : BackwardConsumer) : Set where
  constructor consumer-revision-receipt
  field
    authority : RevisionAuthority
    targetProvenanceIsAuthorised : provenance target ≡ authorisedRevision
    requirementPreserved : strength target ≡ strength source

canonicalAuthorisedRevision : ConsumerRevisionReceipt frozenConsumer authorisedConsumerRevision
canonicalAuthorisedRevision =
  consumer-revision-receipt externalRevisionAuthority refl refl

routeGeneratedWeakeningCannotBeAuthorised :
  ConsumerRevisionReceipt frozenConsumer routeWeakenedConsumer → ⊥
routeGeneratedWeakeningCannotBeAuthorised receipt with
  ConsumerRevisionReceipt.targetProvenanceIsAuthorised receipt
... | ()

------------------------------------------------------------------------
-- Producer success is evaluated against the governed consumer, not a route-local
-- surrogate.
------------------------------------------------------------------------

data CandidateOutput : Set where exactOutput approximateSurrogate : CandidateOutput

data AcceptedBy : BackwardConsumer → CandidateOutput → Set where
  exactAccepted : AcceptedBy frozenConsumer exactOutput
  exactAcceptedAfterAuthorisedRevision : AcceptedBy authorisedConsumerRevision exactOutput

surrogateCannotSatisfyFrozenConsumer : AcceptedBy frozenConsumer approximateSurrogate → ⊥
surrogateCannotSatisfyFrozenConsumer ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record GovernedBackwardConsumerBoundary : Set where
  constructor governed-backward-consumer-boundary
  field
    producerMayRewriteAcceptanceLanguage : Bool
    producerMayRewriteAcceptanceLanguageIsFalse : producerMayRewriteAcceptanceLanguage ≡ false
    routeMayWeakenRequirementToClaimSuccess : Bool
    routeMayWeakenRequirementToClaimSuccessIsFalse : routeMayWeakenRequirementToClaimSuccess ≡ false
    consumerRevisionNeedsExternalAuthority : Bool
    consumerRevisionNeedsExternalAuthorityIsTrue : consumerRevisionNeedsExternalAuthority ≡ true
    authorisedRevisionMayEraseRequirementStrength : Bool
    authorisedRevisionMayEraseRequirementStrengthIsFalse : authorisedRevisionMayEraseRequirementStrength ≡ false
    approximateSurrogateEqualsExactConsumerOutput : Bool
    approximateSurrogateEqualsExactConsumerOutputIsFalse : approximateSurrogateEqualsExactConsumerOutput ≡ false
    reading : String

canonicalGovernedBackwardConsumerBoundary : GovernedBackwardConsumerBoundary
canonicalGovernedBackwardConsumerBoundary =
  governed-backward-consumer-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    "BIDI's backward consumer is capability-protected: acceptance language, active requirements, evidence criteria and residual budgets are not producer-controlled. Consumer revision requires external authority and provenance, and this finite owner preserves requirement strength across authorised revision rather than permitting route-local weakening."

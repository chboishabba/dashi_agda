module DASHI.Culture.AmyEskridgeInstituteDerivativeIdentityJointPaymentBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeInstituteDerivativeIdentityDiscriminatorExact as D
import DASHI.Culture.AmyEskridgeEntityEventTimeCustodySnowballWeldExact as Router
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as App
import DASHI.Culture.AmyEskridgePOAMSBoundaryCandidateExact as Candidate
import DASHI.Core.KnowledgeBoundaryCandidateIdentityBidiExact as Identity

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: JOINT IDENTITY-DISCRIMINATOR PAYMENT WELD
--
-- The existing discriminator owner correctly blocks promotion from topic/team/
-- timeline compatibility alone and exposes several identity-specific routes.
-- This thin adapter handles the case where no single magical identifier is
-- sufficient on its own, but several identity-specific receipts jointly name
-- the same object.  The extra jointSameObjectCoherence field is irreducible:
-- paid marginals do not manufacture exact identity by counting clues.
------------------------------------------------------------------------

record JointIdentityDiscriminatorPayment : Set where
  constructor joint-identity-discriminator-payment
  field
    firstReceipt : D.IdentityDiscriminatorReceipt
    secondReceipt : D.IdentityDiscriminatorReceipt
    thirdReceipt : D.IdentityDiscriminatorReceipt

    firstIsPaid : D.state firstReceipt ≡ D.paid
    secondIsPaid : D.state secondReceipt ≡ D.paid
    thirdIsPaid : D.state thirdReceipt ≡ D.paid

    firstIsIdentitySpecific : D.mayPromoteExactIdentity firstReceipt ≡ true
    secondIsIdentitySpecific : D.mayPromoteExactIdentity secondReceipt ≡ true
    thirdIsIdentitySpecific : D.mayPromoteExactIdentity thirdReceipt ≡ true

    jointSameObjectCoherence : Bool
    jointSameObjectCoherenceIsTrue : jointSameObjectCoherence ≡ true
    jointIdentityReference : String

open JointIdentityDiscriminatorPayment public

------------------------------------------------------------------------
-- Consumer routing.
--
-- The joint receipt does not invent a new application target.  It discharges
-- the same already-existing first unpaid leaf as a single exact discriminator.
------------------------------------------------------------------------

jointPaymentTargetsApplicationLeaf :
  JointIdentityDiscriminatorPayment -> App.AmyApplicationReverseTarget
jointPaymentTargetsApplicationLeaf _ = App.acquireInstituteDerivedObjectIdentity

jointPaymentTargetsCurrentFirstLeaf :
  (joint : JointIdentityDiscriminatorPayment) ->
  jointPaymentTargetsApplicationLeaf joint ≡ App.firstAmyApplicationMissingLeaf
jointPaymentTargetsCurrentFirstLeaf _ = refl

------------------------------------------------------------------------
-- Canonical useful conjunction shape.
--
-- This is intentionally a shape, not a claim that the current receipts are
-- paid.  The three strongest complementary routes are exact title/attachment,
-- versioned draft identity, and same-object correspondence.  Any future/current
-- repo-native receipts inhabiting those routes can be passed directly here.
------------------------------------------------------------------------

record TitleVersionCorrespondenceJointReceipt : Set where
  constructor title-version-correspondence-joint-receipt
  field
    title : D.IdentityDiscriminatorReceipt
    version : D.IdentityDiscriminatorReceipt
    correspondence : D.IdentityDiscriminatorReceipt

    titleTargetsTitle : D.target title ≡ D.exactPaperOrAttachmentTitle
    versionTargetsVersion : D.target version ≡ D.versionedDraftIdentifier
    correspondenceTargetsSameObject :
      D.target correspondence ≡ D.correspondenceSameObjectStatement

    titlePaid : D.state title ≡ D.paid
    versionPaid : D.state version ≡ D.paid
    correspondencePaid : D.state correspondence ≡ D.paid

    titleMayPromote : D.mayPromoteExactIdentity title ≡ true
    versionMayPromote : D.mayPromoteExactIdentity version ≡ true
    correspondenceMayPromote : D.mayPromoteExactIdentity correspondence ≡ true

    sameObjectAcrossAllThree : Bool
    sameObjectAcrossAllThreeIsTrue : sameObjectAcrossAllThree ≡ true
    identityReference : String

open TitleVersionCorrespondenceJointReceipt public

titleVersionCorrespondenceToJointPayment :
  TitleVersionCorrespondenceJointReceipt -> JointIdentityDiscriminatorPayment
titleVersionCorrespondenceToJointPayment receipt =
  joint-identity-discriminator-payment
    (title receipt)
    (version receipt)
    (correspondence receipt)
    (titlePaid receipt)
    (versionPaid receipt)
    (correspondencePaid receipt)
    (titleMayPromote receipt)
    (versionMayPromote receipt)
    (correspondenceMayPromote receipt)
    (sameObjectAcrossAllThree receipt)
    (sameObjectAcrossAllThreeIsTrue receipt)
    (identityReference receipt)

------------------------------------------------------------------------
-- Current negative state remains executable.
--
-- The adapter deliberately does not reinterpret the current unpaid/retained
-- ledger as a joint payment.  This proves the extension is monotone: it opens a
-- new composition route without weakening the existing evidence boundary.
------------------------------------------------------------------------

currentCandidateRemainsStrongNotExact :
  Identity.grade Candidate.poamsCandidate ≡ Identity.strongCandidate
currentCandidateRemainsStrongNotExact = refl

currentTitleStillUnpaid : D.state D.exactTitleReceipt ≡ D.unpaid
currentTitleStillUnpaid = refl

currentVersionStillUnpaid : D.state D.versionedDraftReceipt ≡ D.unpaid
currentVersionStillUnpaid = refl

currentCorrespondenceStillUnpaid :
  D.state D.correspondenceIdentityReceipt ≡ D.unpaid
currentCorrespondenceStillUnpaid = refl

currentWitnessStillRetainedLead :
  D.state D.directWitnessIdentifierLead ≡ D.retainedLead
currentWitnessStillRetainedLead = refl

currentSingleReceiptRouterStillRequiresPaidPromotionEntitlement :
  {receipt : D.IdentityDiscriminatorReceipt} ->
  Router.ExactIdentityPaymentReceipt receipt ->
  App.AmyApplicationReverseTarget
currentSingleReceiptRouterStillRequiresPaidPromotionEntitlement =
  Router.identityReceiptPaysApplicationLeaf

------------------------------------------------------------------------
-- WrongType / joint-precondition firewall.
--
-- This is the evidence analogue of the repo-wide rule that satisfying marginal
-- coordinates is not the same type of object as satisfying their relational
-- consumer.  Counts, compatibility, chronology and source plurality are useful
-- acquisition coordinates; exact same-object promotion consumes an identity-
-- indexed relational receipt.
------------------------------------------------------------------------

record JointIdentityPaymentBoundary : Set where
  constructor joint-identity-payment-boundary
  field
    threePaidMarginalsAutomaticallyMeanSameObject : Bool
    threeCompatibleCluesAutomaticallyMeanSameObject : Bool
    sourcePluralityAutomaticallyMeansSameObject : Bool
    strongCandidateAutomaticallyMeansJointPayment : Bool
    jointCoherenceMayCombinePaidIdentitySpecificReceipts : Bool
    jointPaymentUsesExistingApplicationIdentityConsumer : Bool
    jointPaymentAutomaticallyPaysDownstreamApparatus : Bool
    jointPaymentAutomaticallyPaysDownstreamData : Bool
    jointPaymentAutomaticallyPaysSuccession : Bool
    identityPaymentCreatesDeathCausation : Bool

open JointIdentityPaymentBoundary public

canonicalJointIdentityPaymentBoundary : JointIdentityPaymentBoundary
canonicalJointIdentityPaymentBoundary =
  joint-identity-payment-boundary
    false false false false
    true true
    false false false false

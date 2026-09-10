module DASHI.Culture.AmyEskridgePOAMSSAAAgreementTopologyWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.LayeredKnowledgeReleaseBidiExact as ReleaseCore
import DASHI.Culture.POAMSLayeredReleaseExact as Release
import DASHI.Culture.AmyEskridgePOAMSObjectLineageExact as Lineage
import DASHI.Culture.AmyEskridgePOAMSReviewObjectDisambiguationExact as Review
import DASHI.Culture.AmyEskridgeInstituteDerivativeIdentityDiscriminatorExact as D

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: PRIMARY NASA POAMS SAA TOPOLOGY WELD
--
-- NASA's 31-Dec-2016 active Space Act Agreement register separates three
-- Quantum Machines / MSFC carriers that had previously been compressed in the
-- Amy lane into the parent SAA8-1519855 label:
--
--   SAA8-1519855    Advanced Propulsion Theory and Experimentation
--   SAA8-1519855.1  Advanced Propulsion Theory and Experimentation
--                    POAMS Familiarization
--   SAA8-1519855.2  Advanced Propulsion Theory and Experimental Prototyping
--
-- This is source-specific topology, not a new release ontology.  In particular,
-- an agreement identifier/date proves an agreement carrier; it does not by
-- itself identify Amy's September-2020 NASA-review object or a DAA release case.
------------------------------------------------------------------------

data POAMSAgreementRole : Set where
  parentTheoryExperimentation : POAMSAgreementRole
  poamsFamiliarization : POAMSAgreementRole
  experimentalPrototyping : POAMSAgreementRole

record POAMSAgreementReceipt : Set where
  constructor poams-agreement-receipt
  field
    identifier : String
    role : POAMSAgreementRole
    title : String
    executionDate : String
    expirationDate : String
    partner : String
    center : String
    agreementType : String
    primarySourceReference : String
    exactAgreementIdentityPaid : Bool
    identifiesAmyReviewObject : Bool
    identifiesNASAReleaseCase : Bool
    identifiesInstituteDerivative : Bool

open POAMSAgreementReceipt public

poamsParentAgreement : POAMSAgreementReceipt
poamsParentAgreement = poams-agreement-receipt
  "SAA8-1519855"
  parentTheoryExperimentation
  "Advanced Propulsion Theory and Experimentation"
  "2015-07-01"
  "2020-07-01"
  "Quantum Machines LLC"
  "MSFC"
  "Reimbursable"
  "NASA List of Active Space Act Agreements as of 2016-12-31; NASA/TM-20205010911"
  true false false false

poamsFamiliarizationAgreement : POAMSAgreementReceipt
poamsFamiliarizationAgreement = poams-agreement-receipt
  "SAA8-1519855.1"
  poamsFamiliarization
  "Advanced Propulsion Theory and Experimentation POAMS Familiarization"
  "2015-07-01"
  "2017-07-01"
  "Quantum Machines LLC"
  "MSFC"
  "Reimbursable"
  "NASA List of Active Space Act Agreements as of 2016-12-31"
  true false false false

poamsExperimentalPrototypingAgreement : POAMSAgreementReceipt
poamsExperimentalPrototypingAgreement = poams-agreement-receipt
  "SAA8-1519855.2"
  experimentalPrototyping
  "Advanced Propulsion Theory and Experimental Prototyping"
  "2016-04-08"
  "2018-04-08"
  "Quantum Machines LLC"
  "MSFC"
  "Reimbursable"
  "NASA List of Active Space Act Agreements as of 2016-12-31, PAM 21453"
  true false false false

------------------------------------------------------------------------
-- Source-specific temporal topology.
--
-- The .2 prototyping carrier is active across the 7-Oct-2016 NASA test described
-- by the eventual TM.  This sharpens the earlier-study referent into a family of
-- exact programme carriers, but does not make .2 the unnamed object Amy said was
-- under NASA review in September 2020.
------------------------------------------------------------------------

record POAMSAgreementTemporalTopology : Set where
  constructor poams-agreement-temporal-topology
  field
    parentBeginsJuly2015 : Bool
    familiarizationBeginsJuly2015 : Bool
    prototypingBeginsApril2016 : Bool
    october2016TestFallsInsideParent : Bool
    october2016TestFallsInsideFamiliarization : Bool
    october2016TestFallsInsidePrototyping : Bool
    familiarizationEndsJuly2017 : Bool
    prototypingEndsApril2018 : Bool
    parentEndsJuly2020 : Bool
    parentEndsBeforeAmySeptember2020Statement : Bool
    agreementExpiryEqualsPublicReleaseApproval : Bool

open POAMSAgreementTemporalTopology public

canonicalPOAMSAgreementTemporalTopology : POAMSAgreementTemporalTopology
canonicalPOAMSAgreementTemporalTopology =
  poams-agreement-temporal-topology
    true true true
    true true true
    true true true true
    false

------------------------------------------------------------------------
-- Cross-pollination into existing Amy objects.
------------------------------------------------------------------------

reviewStillHasEarlierNASAStudyReferent :
  Review.ReviewReferentCandidate
reviewStillHasEarlierNASAStudyReferent = Review.earlierNASAStudyReferent

studyStillDistinctFromFinalTM :
  Lineage.earlierStudyDistinctFromLaterTM
    Lineage.canonicalCurrentPOAMSLineageAssessment ≡ true
studyStillDistinctFromFinalTM = refl

existingLayeredReleaseStillRequestsSameObjectWeld :
  ReleaseCore.target Release.poamsNeedsDerivativeIdentity ≡
    ReleaseCore.sameLayerSameObjectWeld
existingLayeredReleaseStillRequestsSameObjectWeld = refl

------------------------------------------------------------------------
-- Discriminator consequence.
--
-- SAA8-1519855.2 is a newly explicit primary programme identifier, but the Amy
-- identity consumer asks for an Amy-linked release/review identifier.  Therefore
-- .2 is retained as a high-value narrowing receipt, not silently upgraded to a
-- paid primaryNASAReleaseIdentifier.
------------------------------------------------------------------------

prototypingAgreementNarrowsEarlierStudyReferent : D.IdentityDiscriminatorReceipt
prototypingAgreementNarrowsEarlierStudyReferent = D.identity-discriminator-receipt
  D.primaryNASAReleaseIdentifier
  D.retainedLead
  "Primary NASA SAA8-1519855.2: Advanced Propulsion Theory and Experimental Prototyping, 2016-04-08 through 2018-04-08; exact programme carrier overlapping the October-2016 test, but not an Amy-linked September-2020 release/review identifier."
  false

record POAMSSAAAgreementTopologyBoundary : Set where
  constructor poams-saa-agreement-topology-boundary
  field
    parentEqualsFamiliarizationAnnex : Bool
    parentEqualsPrototypingAnnex : Bool
    prototypingAgreementEquals2016Experiment : Bool
    prototypingAgreementEquals2021TM : Bool
    agreementExpiryEqualsProprietaryPeriodEnd : Bool
    agreementExpiryEqualsDAAApproval : Bool
    exactProgrammeIdentifierMayNarrowReviewReferent : Bool
    exactProgrammeIdentifierAlonePaysAmyReviewIdentity : Bool
    existingSameObjectWeldRemainsCanonicalConsumer : Bool
    agreementTopologyCreatesDeathCausation : Bool

open POAMSSAAAgreementTopologyBoundary public

canonicalPOAMSSAAAgreementTopologyBoundary : POAMSSAAAgreementTopologyBoundary
canonicalPOAMSSAAAgreementTopologyBoundary =
  poams-saa-agreement-topology-boundary
    false false false false false false
    true false true false

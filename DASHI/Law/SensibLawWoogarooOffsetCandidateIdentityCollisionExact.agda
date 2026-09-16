module DASHI.Law.SensibLawWoogarooOffsetCandidateIdentityCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- OFFSET CANDIDATE IDENTITY COLLISION AUDIT
--
-- Protects against treating a shared place/property name as exact parcel
-- identity.  In particular, 'Avonvale' appears in multiple public conservation
-- and EPBC-offset contexts.  Exact lot/plan/polygon identity remains required.
------------------------------------------------------------------------

data CandidateName : Set where
  avonvale : CandidateName
  esk : CandidateName
  mtWalkerWest : CandidateName

data SourceContext : Set where
  submission20198575 : SourceContext
  avonvaleOtherEPBCOffsetPlan : SourceContext
  avonvaleOtherApprovalCondition : SourceContext
  greenfleetIvoryCreekRestoration : SourceContext
  mtMortRegionalConservation : SourceContext

data IdentityStatus : Set where
  exactIdentityProved : IdentityStatus
  sameNameOnly : IdentityStatus
  sameRegionOnly : IdentityStatus
  identityOpen : IdentityStatus

record CandidateReceipt : Set where
  constructor candidate-receipt
  field
    candidate : CandidateName
    sourceContext : SourceContext
    proposition : String
    provenanceStage : Provenance.LegalClaimProvenanceStage
    identityStatus : IdentityStatus
    mayPay20198575ExactParcel : Bool

open CandidateReceipt public

submissionAvonvale : CandidateReceipt
submissionAvonvale = candidate-receipt
  avonvale
  submission20198575
  "A public submission responding to EPBC 2019/8575 says the proposed offset package offers Avonvale, 168 ha, associated in the submission with regional ecosystem 12.11.14."
  Provenance.secondarySourceInterpretation
  identityOpen
  false

submissionEsk : CandidateReceipt
submissionEsk = candidate-receipt
  esk
  submission20198575
  "A public submission responding to EPBC 2019/8575 says the proposed offset package offers an Esk property, 280 ha, associated in the submission with regional ecosystem 12.9/10.2."
  Provenance.secondarySourceInterpretation
  identityOpen
  false

submissionMtWalkerWest : CandidateReceipt
submissionMtWalkerWest = candidate-receipt
  mtWalkerWest
  submission20198575
  "A public submission responding to EPBC 2019/8575 says the proposed offset package offers a Mt Walker West property, 225 ha, associated in the submission with regional ecosystem 12.8.16."
  Provenance.secondarySourceInterpretation
  identityOpen
  false

otherAvonvaleOMP : CandidateReceipt
otherAvonvaleOMP = candidate-receipt
  avonvale
  avonvaleOtherEPBCOffsetPlan
  "A separate public Avonvale/Cherry Gully Offset Management Plan for another EPBC project describes Avonvale offset vegetation including non-remnant/sparse juvenile vegetation and pre-clear regional ecosystem 12.9-10.7."
  Provenance.externalSourceClaim
  sameNameOnly
  false

otherAvonvaleApproval : CandidateReceipt
otherAvonvaleApproval = candidate-receipt
  avonvale
  avonvaleOtherApprovalCondition
  "A separate EPBC approval condition requires at least 183 ha to be legally secured within the Avonvale and Cherry Gully Offset Area for another action."
  Provenance.externalSourceClaim
  sameNameOnly
  false

greenfleetAvonvale : CandidateReceipt
greenfleetAvonvale = candidate-receipt
  avonvale
  greenfleetIvoryCreekRestoration
  "Greenfleet publicly identifies an Avonvale property as one of four Ivory Creek properties being restored/revegetated."
  Provenance.externalSourceClaim
  sameNameOnly
  false

------------------------------------------------------------------------
-- Cross-source residuals.  These are repository inferences/questions only.
------------------------------------------------------------------------

record CollisionResidual : Set where
  constructor collision-residual
  field
    question : String
    provenanceStage : Provenance.LegalClaimProvenanceStage
    exactIdentityNeeded : Bool
    currentlyPaid : Bool

open CollisionResidual public

avonvaleIdentityResidual : CollisionResidual
avonvaleIdentityResidual = collision-residual
  "Is the 168 ha Avonvale named in the 2019/8575 submission the same cadastral land, overlapping land, adjacent land, or unrelated land to the Avonvale/Cherry Gully offset areas and Greenfleet Avonvale property described in other public sources?"
  Provenance.crossSourceInference
  true
  false

avonvalePriorProtectionResidual : CollisionResidual
avonvalePriorProtectionResidual = collision-residual
  "If exact polygon overlap exists, what part of the proposed 2019/8575 conservation gain is already legally secured, restoration-funded, or committed to another offset, and what additional gain remains available?"
  Provenance.crossSourceInference
  true
  false

avonvaleRegionalEcosystemResidual : CollisionResidual
avonvaleRegionalEcosystemResidual = collision-residual
  "Why does the 2019/8575 submission describe Avonvale as RE 12.11.14 while another Avonvale offset plan describes relevant vegetation/pre-clear mapping as RE 12.9-10.7? Determine whether this reflects different parcels/portions, different mapping layers, or an error before making any comparison."
  Provenance.crossSourceInference
  true
  false

record CollisionBoundary : Set where
  constructor collision-boundary
  field
    sameNameDoesNotProveSameParcel : Bool
    sameOwnerDoesNotProveSamePolygon : Bool
    sameRegionalEcosystemLabelDoesNotProveSameObject : Bool
    differentRegionalEcosystemLabelDoesNotProveDifferentProperty : Bool
    priorOffsetNearbyDoesNotProveDoubleCounting : Bool
    restorationNearbyDoesNotProvePriorProtectionOfExactParcel : Bool
    secondarySubmissionDoesNotProveFinalOffsetPackage : Bool

collisionBoundary : CollisionBoundary
collisionBoundary = collision-boundary true true true true true true true

record CurrentCollisionState : Set where
  constructor current-collision-state
  field
    threeCandidateNamesSecondaryPaid : Bool
    avonvaleSameNamePublicContextsFound : Bool
    exactLotPlansPaid : Bool
    exactPolygonOverlapPaid : Bool
    priorProtectionOverlapPaid : Bool
    doubleCountingProved : Bool

currentCollisionState : CurrentCollisionState
currentCollisionState = current-collision-state true true false false false false

module DASHI.Interop.SensibLawNatPeerPressureWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawNatZelphPeerCohortExact as Peer
import DASHI.Interop.SensibLawWikidataItemPropertyEvidenceExact as Item

------------------------------------------------------------------------
-- Runtime parity owner for src/policy/nat_climate_peer_pressure.py.
--
-- The existing Nat climate pressure assessment owns all non-peer residuals.
-- This weld replaces exactly the peer_cohort coordinate from governed item
-- evidence + invariant evidence; it does not rebuild or strengthen the rest.
------------------------------------------------------------------------

record ExistingNatPressureAssessment : Set where
  constructor existing-nat-pressure-assessment
  field
    candidateReference : String
    targetModelResidualReference : String
    subjectTypeResidualReference : String
    qualifierResidualReference : String
    referenceResidualReference : String
    temporalResidualReference : String
    splitResidualReference : String
    peerResidualReference : String
    authorityIsDiagnosticOnly : Bool
    authorityIsDiagnosticOnlyIsTrue : authorityIsDiagnosticOnly ≡ true
    promotionEvaluated : Bool
    promotionEvaluatedIsFalse : promotionEvaluated ≡ false
    editEffect : Bool
    editEffectIsFalse : editEffect ≡ false
open ExistingNatPressureAssessment public

record NatPeerPressureWeldInput : Set where
  constructor nat-peer-pressure-weld-input
  field
    existingAssessment : ExistingNatPressureAssessment
    itemEvidence : Item.ItemPropertyEvidenceSurface
    peerAssessment : Peer.NatPeerCohortAssessment
open NatPeerPressureWeldInput public

record WeldedNatPressureAssessment : Set where
  constructor welded-nat-pressure-assessment
  field
    originalAssessmentReference : String
    replacementPeerResidualReference : String
    allNonPeerResidualsPreserved : Bool
    allNonPeerResidualsPreservedIsTrue : allNonPeerResidualsPreserved ≡ true
    authorityPreserved : Bool
    authorityPreservedIsTrue : authorityPreserved ≡ true
    promotionStatePreserved : Bool
    promotionStatePreservedIsTrue : promotionStatePreserved ≡ true
    editStatePreserved : Bool
    editStatePreservedIsTrue : editStatePreserved ≡ true
open WeldedNatPressureAssessment public

data PeerWeldMayRewriteTargetModelResidual : Set where
data PeerWeldMayRewriteTemporalResidual : Set where
data PeerWeldCreatesPromotionAuthority : Set where
data PeerWeldCreatesEditAuthority : Set where

peerWeldDoesNotRewriteTargetModel :
  PeerWeldMayRewriteTargetModelResidual → ⊥
peerWeldDoesNotRewriteTargetModel ()

peerWeldDoesNotRewriteTemporal :
  PeerWeldMayRewriteTemporalResidual → ⊥
peerWeldDoesNotRewriteTemporal ()

peerWeldDoesNotCreatePromotionAuthority :
  PeerWeldCreatesPromotionAuthority → ⊥
peerWeldDoesNotCreatePromotionAuthority ()

peerWeldDoesNotCreateEditAuthority :
  PeerWeldCreatesEditAuthority → ⊥
peerWeldDoesNotCreateEditAuthority ()

record NatPeerPressureWeldBoundary : Set where
  constructor nat-peer-pressure-weld-boundary
  field
    replacesOnlyPeerCoordinate : Bool
    preservesOtherResiduals : Bool
    preservesDiagnosticAuthority : Bool
    createsPromotion : Bool
    createsEdit : Bool

canonicalNatPeerPressureWeldBoundary : NatPeerPressureWeldBoundary
canonicalNatPeerPressureWeldBoundary =
  nat-peer-pressure-weld-boundary true true true false false

natPeerPressureWeldStatement : String
natPeerPressureWeldStatement =
  "The Nat peer-pressure weld is least privilege: governed item/cohort evidence may replace exactly the peer_cohort residual of an already-built climate pressure assessment. Target-model, subject, qualifier, reference, temporal and split residuals remain owned by their existing producers, while diagnostic authority, promotion state and edit state are preserved unchanged."

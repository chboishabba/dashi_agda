module DASHI.Chemistry.EvidenceObligationAuthorityBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as Neurochemical
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant

------------------------------------------------------------------------
-- Chemistry instantiation of evidence / obligation / authority separation.
--
-- Existing chemistry already separates candidate observations from exact
-- references, measurement authority, preservation tokens, protocol provenance,
-- replication, and downstream clinical/pharmacological authority.  This module
-- simply places those boundaries on the generic three-coordinate claim state.
------------------------------------------------------------------------

chemistryCandidateSupportedButNotPromotable : Governed.GovernedClaimState
chemistryCandidateSupportedButNotPromotable =
  Governed.governedClaimState
    (Four.assess true false)
    Governed.obligationsOpen
    Governed.authorityDenied

chemistryCandidateSupportDoesNotPromote :
  Governed.promotionGate chemistryCandidateSupportedButNotPromotable ≡ false
chemistryCandidateSupportDoesNotPromote = refl

chemistryObligationsDischargedStillNeedAuthority : Governed.GovernedClaimState
chemistryObligationsDischargedStillNeedAuthority =
  Governed.governedClaimState
    (Four.assess true false)
    Governed.obligationsDischarged
    Governed.authorityDenied

chemistryDischargeDoesNotGrantAuthority :
  Governed.promotionGate chemistryObligationsDischargedStillNeedAuthority ≡ false
chemistryDischargeDoesNotGrantAuthority = refl

clinicalAuthorityRouteStillRejected :
  Neurochemical.AdmissibleNeurochemicalAtomicChemistryRoute
    Neurochemical.clinicalAuthorityRoute →
  Neurochemical.Never
clinicalAuthorityRouteStillRejected = Neurochemical.clinicalAuthorityRejected

record ChemistryEvidenceObligationAuthorityBoundary : Set where
  field
    quantitativeRequirementsRemainIndependent : Bool
    wetLabReplicationRemainsIndependent : Bool
    candidateSupportEqualsMolecularAuthorityClaimed : Bool
    technicalDischargeEqualsClinicalAuthorityClaimed : Bool
    genericGovernedClaimStateReused : Bool

canonicalChemistryEvidenceObligationAuthorityBoundary :
  ChemistryEvidenceObligationAuthorityBoundary
canonicalChemistryEvidenceObligationAuthorityBoundary = record
  { quantitativeRequirementsRemainIndependent = true
  ; wetLabReplicationRemainsIndependent = true
  ; candidateSupportEqualsMolecularAuthorityClaimed = false
  ; technicalDischargeEqualsClinicalAuthorityClaimed = false
  ; genericGovernedClaimStateReused = true
  }

quantitativeAdapterBoundaryReused : Quant.ChemistryQuantitativeAdapter
quantitativeAdapterBoundaryReused = Quant.canonicalChemistryQuantitativeAdapter

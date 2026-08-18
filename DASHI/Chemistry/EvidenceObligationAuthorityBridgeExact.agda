module DASHI.Chemistry.EvidenceObligationAuthorityBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as Neurochemical
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Promotion.AuthorityGateCore as Authority
import DASHI.Promotion.ChemistryAuthorityBinding as Binding
import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant

------------------------------------------------------------------------
-- Chemistry instantiation of evidence / obligation / authority separation.
--
-- Existing chemistry already separates candidate observations from exact
-- references, quantitative-law carriers, measurement authority, preservation
-- tokens, protocol provenance, replication, and downstream clinical/
-- pharmacological authority.  The existing ChemistryAuthorityBinding further
-- supplies concrete NIST/CODATA authority-token shapes, all fail-closed until
-- provenance/checksum/uncertainty requirements are actually discharged.
------------------------------------------------------------------------

chemistryCandidateSupportedButNotPromotable : Governed.GovernedClaimState
chemistryCandidateSupportedButNotPromotable =
  Governed.closedGovernedClaimState
    (Four.assess true false)
    Governed.obligationsOpen
    Authority.scientificAuthority
    "chemistry candidate to scientific authority"

chemistryCandidateSupportDoesNotPromote :
  Governed.localPromotion chemistryCandidateSupportedButNotPromotable ≡ false
chemistryCandidateSupportDoesNotPromote =
  Governed.localPromotionIsFalse chemistryCandidateSupportedButNotPromotable

chemistryObligationsDischargedStillNeedAuthority : Governed.GovernedClaimState
chemistryObligationsDischargedStillNeedAuthority =
  Governed.closedGovernedClaimState
    (Four.assess true false)
    Governed.obligationsDischarged
    Authority.scientificAuthority
    "chemistry technical obligations discharged but external authority gate closed"

chemistryDischargeDoesNotGrantAuthority :
  Governed.localPromotion chemistryObligationsDischargedStillNeedAuthority ≡ false
chemistryDischargeDoesNotGrantAuthority =
  Governed.localPromotionIsFalse chemistryObligationsDischargedStillNeedAuthority

clinicalAuthorityRouteStillRejected :
  Neurochemical.AdmissibleNeurochemicalAtomicChemistryRoute
    Neurochemical.clinicalAuthorityRoute →
  Neurochemical.Never
clinicalAuthorityRouteStillRejected = Neurochemical.clinicalAuthorityRejected

chemistryAuthorityBindingsReused : List Binding.AuthorityTokenBinding
chemistryAuthorityBindingsReused = Binding.canonicalAuthorityTokenBindings

record ChemistryEvidenceObligationAuthorityBoundary : Set where
  field
    quantitativeRequirementsRemainIndependent : Bool
    wetLabReplicationRemainsIndependent : Bool
    candidateSupportEqualsMolecularAuthorityClaimed : Bool
    technicalDischargeEqualsClinicalAuthorityClaimed : Bool
    chemistryAuthorityBindingReused : Bool
    canonicalAuthorityGateCoreReused : Bool

canonicalChemistryEvidenceObligationAuthorityBoundary :
  ChemistryEvidenceObligationAuthorityBoundary
canonicalChemistryEvidenceObligationAuthorityBoundary = record
  { quantitativeRequirementsRemainIndependent = true
  ; wetLabReplicationRemainsIndependent = true
  ; candidateSupportEqualsMolecularAuthorityClaimed = false
  ; technicalDischargeEqualsClinicalAuthorityClaimed = false
  ; chemistryAuthorityBindingReused = true
  ; canonicalAuthorityGateCoreReused = true
  }

quantitativeAdapterBoundaryReused : Quant.ChemistryQuantitativeAdapter
quantitativeAdapterBoundaryReused = Quant.canonicalChemistryQuantitativeAdapter

module DASHI.Governance.BoloBoloExternalControlProvenanceWeldExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Reasoning.ReleasedArtifactProvenanceBidiExact as Released
import DASHI.Governance.RelationPolicyTransportComposition as Relation
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Palantir
import DASHI.Economics.NvidiaCoreWeaveReflexiveInvestment2026Exact as Financing

------------------------------------------------------------------------
-- EXTERNAL-CONTROL PROVENANCE WELD
--
-- This is attribution/provenance machinery only.  It deliberately blocks the
-- most tempting cross-domain collapses when Thiel/Palantir, asset-manager /
-- private-capital, and Epstein/relation evidence are viewed together.
------------------------------------------------------------------------

releasedArtifactBoundaryAnchor : Released.ReleasedArtifactPromotionBoundary
releasedArtifactBoundaryAnchor = Released.canonicalReleasedArtifactPromotionBoundary

palantirBoundaryAnchor : Palantir.PalantirCapabilityBoundary
palantirBoundaryAnchor = Palantir.canonicalPalantirCapabilityBoundary

financingCalibrationAnchor : Financing.VendorCustomerReflexivityCalibration
financingCalibrationAnchor = Financing.canonicalVendorCustomerReflexivityCalibration

relationPathDoesNotAutomaticallyInheritProposition :
  ∀ {R} {path : Relation.TwoStepRelationPath R} →
  Relation.PathAutomaticallyInheritsProposition path → ⊥
relationPathDoesNotAutomaticallyInheritProposition =
  Relation.pathDoesNotAutomaticallyInheritProposition

record ExternalControlProvenanceBoundary : Set where
  constructor external-control-provenance-boundary
  field
    officialReleasePaysEmbeddedClaimTruth : Bool
    officialReleasePaysInstitutionalEndorsement : Bool
    officialReleasePaysInstitutionalVerification : Bool
    relationReachabilityPaysInfluence : Bool
    relationReachabilityPaysKnowledge : Bool
    relationReachabilityPaysCulpability : Bool
    corporateRolePaysDeploymentAuthority : Bool
    platformCapabilityPaysObservedDeploymentAsymmetry : Bool
    financingParticipationPaysCommonControl : Bool
    financingParticipationPaysFraud : Bool
    commonFirmNameAcrossSourcesPaysSameObjectControl : Bool
    sourceAgreementPaysUnifiedCommand : Bool
    sameObjectAuthorityAndTransportReceiptsRequired : Bool

open ExternalControlProvenanceBoundary public

canonicalExternalControlProvenanceBoundary : ExternalControlProvenanceBoundary
canonicalExternalControlProvenanceBoundary =
  external-control-provenance-boundary
    false false false
    false false false
    false false false false false false
    true

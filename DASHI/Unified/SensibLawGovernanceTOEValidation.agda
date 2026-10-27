{-# OPTIONS --safe #-}
module DASHI.Unified.SensibLawGovernanceTOEValidation where

------------------------------------------------------------------------
-- Focused facade regression for SensibLaw / legal governance TOE wiring.
--
-- The normalization owner is authoritative for this adapter layer.
-- The imported semantic, legal, parity, and governance modules remain the
-- mathematical and domain theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.SensibLawGovernanceTOEExact as Governance
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Physics as UnifiedPhysics
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain
import DASHI.Law.SensibLawAgdaFirstLegalRuntimeEverything as LegalRuntime

------------------------------------------------------------------------
-- Root agreement.
------------------------------------------------------------------------

toeSemanticBoundaryMatchesOwner :
  TOE.toeSensibLawGovernanceSemanticBoundary
  ≡ Governance.governanceSemanticAuthorityBoundary
toeSemanticBoundaryMatchesOwner =
  refl

toeLegalRuntimeMatchesOwner :
  TOE.toeSensibLawLegalRuntimeContract
  ≡ Governance.governanceLegalRuntimeContract
toeLegalRuntimeMatchesOwner =
  refl

toeDomainTransportMatchesOwner :
  TOE.toeSensibLawDomainTransportReceipt
  ≡ Governance.governanceDomainTransportReceipt
toeDomainTransportMatchesOwner =
  refl

toeZKPFrameMatchesOwner :
  TOE.toeSensibLawGovernanceZKPFrame
  ≡ Governance.canonicalSensibLawGovernanceTOEZKPFrame
toeZKPFrameMatchesOwner =
  refl

toeLegalAuthorityStillClosed :
  Authority.legalAuthorityFlag
    TOE.toeSensibLawGovernanceSemanticBoundary
  ≡ false
toeLegalAuthorityStillClosed =
  TOE.toeSensibLawSemanticLegalAuthorityStillClosed

toeAllAuthorityStillClosed :
  Authority.promotesAnyAuthority
    TOE.toeSensibLawGovernanceSemanticBoundary
  ≡ false
toeAllAuthorityStillClosed =
  TOE.toeSensibLawSemanticAllAuthorityStillClosed

toeRepresentationEqualityDoesNotCreateLegalAuthority :
  Domain.representationEqualityCreatesLegalAuthority
    TOE.toeSensibLawDomainTransportReceipt
  ≡ false
toeRepresentationEqualityDoesNotCreateLegalAuthority =
  TOE.toeSensibLawRepresentationEqualityDoesNotCreateLegalAuthority

toeTargetDomainNeedsOwnAuthorityWitness :
  Domain.targetDomainNeedsOwnAuthorityWitness
    TOE.toeSensibLawDomainTransportReceipt
  ≡ true
toeTargetDomainNeedsOwnAuthorityWitness =
  TOE.toeSensibLawTargetDomainNeedsOwnAuthorityWitness

------------------------------------------------------------------------
-- Unifier agreement.
------------------------------------------------------------------------

unifierSemanticBoundaryMatchesOwner :
  Unifier.unifierSensibLawGovernanceSemanticBoundary
  ≡ Governance.governanceSemanticAuthorityBoundary
unifierSemanticBoundaryMatchesOwner =
  refl

unifierLegalRuntimeMatchesOwner :
  Unifier.unifierSensibLawLegalRuntimeContract
  ≡ Governance.governanceLegalRuntimeContract
unifierLegalRuntimeMatchesOwner =
  refl

unifierDomainTransportMatchesOwner :
  Unifier.unifierSensibLawDomainTransportReceipt
  ≡ Governance.governanceDomainTransportReceipt
unifierDomainTransportMatchesOwner =
  refl

unifierZKPFrameMatchesOwner :
  Unifier.unifierSensibLawGovernanceZKPFrame
  ≡ Governance.canonicalSensibLawGovernanceTOEZKPFrame
unifierZKPFrameMatchesOwner =
  refl

unifierLegalAuthorityStillClosed :
  Authority.legalAuthorityFlag
    Unifier.unifierSensibLawGovernanceSemanticBoundary
  ≡ false
unifierLegalAuthorityStillClosed =
  Unifier.unifierSensibLawSemanticLegalAuthorityStillClosed

unifierAllAuthorityStillClosed :
  Authority.promotesAnyAuthority
    Unifier.unifierSensibLawGovernanceSemanticBoundary
  ≡ false
unifierAllAuthorityStillClosed =
  Unifier.unifierSensibLawSemanticAllAuthorityStillClosed

unifierVendorIdentityDoesNotCreateAuthority :
  Domain.vendorIdentityCreatesAuthority
    Unifier.unifierSensibLawDomainTransportReceipt
  ≡ false
unifierVendorIdentityDoesNotCreateAuthority =
  Unifier.unifierSensibLawVendorIdentityDoesNotCreateAuthority

------------------------------------------------------------------------
-- Unified facade agreement.
------------------------------------------------------------------------

unifiedSemanticBoundaryMatchesOwner :
  UnifiedPhysics.governanceSensibLawSemanticBoundary
  ≡ Governance.governanceSemanticAuthorityBoundary
unifiedSemanticBoundaryMatchesOwner =
  refl

unifiedLegalRuntimeMatchesOwner :
  UnifiedPhysics.governanceSensibLawLegalRuntimeContract
  ≡ Governance.governanceLegalRuntimeContract
unifiedLegalRuntimeMatchesOwner =
  refl

unifiedDomainTransportMatchesOwner :
  UnifiedPhysics.governanceSensibLawDomainTransportReceipt
  ≡ Governance.governanceDomainTransportReceipt
unifiedDomainTransportMatchesOwner =
  refl

unifiedZKPFrameMatchesOwner :
  UnifiedPhysics.governanceSensibLawZKPFrame
  ≡ Governance.canonicalSensibLawGovernanceTOEZKPFrame
unifiedZKPFrameMatchesOwner =
  refl

unifiedLegalAuthorityStillClosed :
  Authority.legalAuthorityFlag
    UnifiedPhysics.governanceSensibLawSemanticBoundary
  ≡ false
unifiedLegalAuthorityStillClosed =
  UnifiedPhysics.governanceSensibLawSemanticLegalAuthorityStillClosed

unifiedAllAuthorityStillClosed :
  Authority.promotesAnyAuthority
    UnifiedPhysics.governanceSensibLawSemanticBoundary
  ≡ false
unifiedAllAuthorityStillClosed =
  UnifiedPhysics.governanceSensibLawSemanticAllAuthorityStillClosed

unifiedRepresentationEqualityDoesNotCreateLegalAuthority :
  Domain.representationEqualityCreatesLegalAuthority
    UnifiedPhysics.governanceSensibLawDomainTransportReceipt
  ≡ false
unifiedRepresentationEqualityDoesNotCreateLegalAuthority =
  UnifiedPhysics.governanceSensibLawRepresentationEqualityDoesNotCreateLegalAuthority

------------------------------------------------------------------------
-- Owner-level invariant pins.
------------------------------------------------------------------------

semanticPromotionCannotGrantLegalAuthority :
  Authority.legalAuthorityFlag
    Governance.governanceSemanticAuthorityBoundary
  ≡ false
semanticPromotionCannotGrantLegalAuthority =
  Governance.governanceSemanticLegalAuthorityStillClosed

runtimeTransportCannotPromoteTruth :
  LegalRuntime.parserCandidateMayBecomeTruthByTransport
    Governance.governanceLegalRuntimeContract
  ≡ false
runtimeTransportCannotPromoteTruth =
  Governance.governanceParserCandidateCannotBecomeTruthByTransport

caseManagementReuseRequiresTargetAuthority :
  Domain.targetDomainNeedsOwnAuthorityWitness
    Governance.governanceDomainTransportReceipt
  ≡ true
caseManagementReuseRequiresTargetAuthority =
  Governance.governanceTargetDomainNeedsOwnAuthorityWitness

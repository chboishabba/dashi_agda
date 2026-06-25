module DASHI.Core.InterconnectionExistingCoreBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as AuthorityBoundary
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.ComparisonLawCore as Comparison
import DASHI.Core.FibreRestrictionCore as Restriction
import DASHI.Core.FingerprintProjectionCore as Fingerprint
import DASHI.Core.HiddenLiftProjectionCore as HiddenLift
import DASHI.Core.LensKernel as LensKernel
import DASHI.Core.ObservableContactGeometry as Geometry
import DASHI.Core.StatisticalEvidenceCore as Statistical

------------------------------------------------------------------------
-- Existing-core bridge.
--
-- This module does not replace older DASHI cores. It records that the new
-- comparison/restriction/contact layer is a compression of those surfaces:
--
-- lens observation              -> comparison surface
-- fingerprint projection        -> fibre/preimage restriction surface
-- hidden-lift projection        -> carrier/public contact surface
-- statistical evidence          -> non-promoting fibre restriction
-- authority boundary            -> contact promotion block
-- bridge requirement            -> promotion prerequisite
------------------------------------------------------------------------

record Witness : Set where
  constructor witness

------------------------------------------------------------------------
-- LensKernel -> ComparisonLawCore
------------------------------------------------------------------------

lensKernelGivesComparisonSurface :
  {S A : Set} →
  LensKernel.Lens S A →
  Comparison.ComparisonLawCore
lensKernelGivesComparisonSurface {S} {A} lens =
  Comparison.comparisonLawCore
    S
    A
    A
    (LensKernel.Lens.observe lens)
    (λ observable → observable)
    (λ left right → left ≡ right)
    (λ left right → left ≡ right)

------------------------------------------------------------------------
-- FingerprintProjectionCore -> FibreRestrictionCore
------------------------------------------------------------------------

fingerprintCollisionGivesFibreRestriction :
  (core : Fingerprint.FingerprintProjectionCore) →
  Restriction.FibreRestrictionCore
fingerprintCollisionGivesFibreRestriction core =
  Restriction.fibreRestrictionCore
    (Fingerprint.objectType core)
    (Fingerprint.digestType core)
    (Fingerprint.digestType core)
    (Fingerprint.objectToDigest core)
    (λ digest → Fingerprint.Fiber core)
    (λ evidence surface → surface ≡ evidence)
    true
    false

record FingerprintRestrictionReceipt : Set where
  constructor fingerprintRestrictionReceipt
  field
    fibreRestrictionCandidateOnly : Bool
    fibreRestrictionCandidateOnlyIsTrue : fibreRestrictionCandidateOnly ≡ true
    fibreRestrictionPromotesTruth : Bool
    fibreRestrictionPromotesTruthIsFalse : fibreRestrictionPromotesTruth ≡ false

canonicalFingerprintRestrictionReceipt : FingerprintRestrictionReceipt
canonicalFingerprintRestrictionReceipt =
  fingerprintRestrictionReceipt
    true
    refl
    false
    refl

------------------------------------------------------------------------
-- HiddenLiftProjectionCore -> ObservableContactGeometry
------------------------------------------------------------------------

hiddenLiftGivesCarrierProjection :
  HiddenLift.HiddenLiftProjectionSurface →
  Geometry.ObservableContactGeometry
hiddenLiftGivesCarrierProjection surface =
  Geometry.observableContactGeometry
    HiddenLift.PrivateCoordinateSpace
    HiddenLift.PublicQuotientSpace
    HiddenLift.PublicQuotientSpace
    HiddenLift.HiddenLiftWitness
    (λ carrier → HiddenLift.publicQuotientProjection)
    (λ observable → HiddenLift.HiddenLiftWitness)
    (λ trace → trace)
    (λ left right → left ≡ right)
    (λ left right → left ≡ right)
    (λ evidence observable → HiddenLift.HiddenLiftWitness)
    true
    false
    (λ left right → Witness)
    Witness

record HiddenLiftContactReceipt : Set where
  constructor hiddenLiftContactReceipt
  field
    hiddenCarrierProjected : Bool
    hiddenCarrierProjectedIsTrue : hiddenCarrierProjected ≡ true
    bridgeCandidateOnly : Bool
    bridgeCandidateOnlyIsTrue : bridgeCandidateOnly ≡ true
    bridgePromoted : Bool
    bridgePromotedIsFalse : bridgePromoted ≡ false

hiddenLiftContactBridgeReceipt :
  (surface : HiddenLift.HiddenLiftProjectionSurface) →
  HiddenLiftContactReceipt
hiddenLiftContactBridgeReceipt surface =
  hiddenLiftContactReceipt
    true
    refl
    true
    refl
    false
    refl

------------------------------------------------------------------------
-- StatisticalEvidenceCore -> FibreRestrictionCore
------------------------------------------------------------------------

statisticalEvidenceRestrictsButDoesNotPromote :
  Statistical.StatisticalEvidenceSurface →
  Restriction.FibreRestrictionCore
statisticalEvidenceRestrictsButDoesNotPromote surface =
  Restriction.fibreRestrictionCore
    Statistical.StatisticalEvidenceSurface
    String
    String
    Statistical.StatisticalEvidenceSurface.evidenceSurface
    (λ label → Statistical.StatisticalEvidenceSurface)
    (λ evidence observable → Witness)
    true
    false

record StatisticalRestrictionReceipt : Set where
  constructor statisticalRestrictionReceipt
  field
    evidenceRestrictsFibre : Bool
    evidenceRestrictsFibreIsTrue : evidenceRestrictsFibre ≡ true
    evidenceRecoversCarrier : Bool
    evidenceRecoversCarrierIsFalse : evidenceRecoversCarrier ≡ false
    evidencePromotesTruth : Bool
    evidencePromotesTruthIsFalse : evidencePromotesTruth ≡ false

statisticalEvidenceBridgeReceipt :
  (surface : Statistical.StatisticalEvidenceSurface) →
  StatisticalRestrictionReceipt
statisticalEvidenceBridgeReceipt surface =
  statisticalRestrictionReceipt
    true
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- AuthorityBoundary -> contact promotion block
------------------------------------------------------------------------

record ContactGateReceipt : Set where
  constructor contactGateReceipt
  field
    externalAuthorityRequired : Bool
    externalAuthorityRequiredIsTrue : externalAuthorityRequired ≡ true
    authorityGateClosed : Bool
    authorityGateClosedIsFalse : authorityGateClosed ≡ false
    contactPromoted : Bool
    contactPromotedIsFalse : contactPromoted ≡ false

authorityBoundaryBlocksContactPromotion :
  AuthorityBoundary.CitationAuthorityNoArtifact →
  ContactGateReceipt
authorityBoundaryBlocksContactPromotion boundary =
  contactGateReceipt
    true
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- BridgeRequirementCore -> promotion prerequisite
------------------------------------------------------------------------

record PromotionPrerequisiteReceipt : Set where
  constructor promotionPrerequisiteReceipt
  field
    bridgeIsPrerequisite : Bool
    bridgeIsPrerequisiteIsTrue : bridgeIsPrerequisite ≡ true
    bridgeCandidateOnly : Bool
    bridgeCandidateOnlyIsTrue : bridgeCandidateOnly ≡ true
    bridgePromotesAuthority : Bool
    bridgePromotesAuthorityIsFalse : bridgePromotesAuthority ≡ false

bridgeRequirementIsPromotionPrerequisite :
  PromotionPrerequisiteReceipt
bridgeRequirementIsPromotionPrerequisite =
  promotionPrerequisiteReceipt
    true
    refl
    (Bridge.rowCandidateOnly Bridge.suppliedCandidateOnlyBridgeRow)
    refl
    (Bridge.rowAuthorityPromotion Bridge.suppliedCandidateOnlyBridgeRow)
    refl

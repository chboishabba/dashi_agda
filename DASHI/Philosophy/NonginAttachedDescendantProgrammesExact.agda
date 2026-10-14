module DASHI.Philosophy.NonginAttachedDescendantProgrammesExact where

------------------------------------------------------------------------
-- NONGIN -> ATTACHED DESCENDANT PROGRAMMES
--
-- These programmes already exist in-repo.  This owner fixes the roadmap
-- mistake of treating them as detached/optional research.  They remain
-- attached descendants of the Nongin lineage while retaining their own
-- promotion boundaries and independent theorem/source ownership.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.RelationalTransportDescentSheafExact as StackLike
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.TrialecticHigherDescentPromotionLedgerExact as Higher
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Promotion.ClassicalFieldObligations as Physical

stackLikeBoundary : StackLike.RelationalTransportDescentBoundary
stackLikeBoundary = StackLike.canonicalRelationalTransportDescentBoundary

hyperfabricBoundary : Hyperfabric.TypedHyperfabricAuthorityBoundary
hyperfabricBoundary = Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary

higherBoundary : Higher.TrialecticHigherDescentPromotionBoundary
higherBoundary = Higher.canonicalTrialecticHigherDescentPromotionBoundary

exceptionalBoundary : Exceptional.ExceptionalResidualBoundary
exceptionalBoundary = Exceptional.canonicalExceptionalResidualBoundary

physicalCarrier : Physical.LawCarrierObligation
physicalCarrier = Physical.canonicalPhysicalLawCarrierObligation

transportAwareDescentAlreadyInRepo :
  StackLike.matchingMayUseTypedTransport stackLikeBoundary ≡ true
transportAwareDescentAlreadyInRepo = refl

holonomyResidualAlreadyRetained :
  StackLike.holonomyResidualRetained stackLikeBoundary ≡ true
holonomyResidualAlreadyRetained = refl

hyperfabricStalkRestrictionOwnerAlreadyInRepo :
  Hyperfabric.restrictionMapsRepresentable hyperfabricBoundary ≡ true
hyperfabricStalkRestrictionOwnerAlreadyInRepo = refl

higherArityHyperfabricAlreadyInRepo :
  Hyperfabric.higherArityRelationsRepresentable hyperfabricBoundary ≡ true
higherArityHyperfabricAlreadyInRepo = refl

exceptionalAlbertF4E6FreudenthalOwnerAlreadyInRepo :
  Exceptional.freudenthal56To54To53ActionInterfaceRecorded exceptionalBoundary ≡ true
exceptionalAlbertF4E6FreudenthalOwnerAlreadyInRepo = refl

physicalPromotionCarrierAlreadyInRepo :
  Physical.carrierSupplied physicalCarrier ≡ true
physicalPromotionCarrierAlreadyInRepo = refl

physicalPromotionGuardStillOwnedByPhysicsLane :
  Physical.lawPromoted physicalCarrier ≡ false
physicalPromotionGuardStillOwnedByPhysicsLane = refl

transportEnrichedTrialecticCertificationStillLocalFrontier :
  Higher.groupoidPresheafReady higherBoundary ≡ false
transportEnrichedTrialecticCertificationStillLocalFrontier = refl

higherStackCertificationStillLocalFrontier :
  Higher.effectiveStackReady higherBoundary ≡ false
higherStackCertificationStillLocalFrontier = refl

hypersheafCertificationStillLocalFrontier :
  Higher.hypersheafReady higherBoundary ≡ false
hypersheafCertificationStillLocalFrontier = refl

record NonginAttachedDescendantProgrammesBoundary : Set where
  constructor nongin-attached-descendant-programmes-boundary
  field
    transportStackLikeOwnerAttached : Bool
    hyperfabricOwnerAttached : Bool
    higherDescentOwnerAttached : Bool
    exceptionalProgrammeAttached : Bool
    physicalPromotionProgrammeAttached : Bool
    descendantProgrammesRemainAttachedToNongin : Bool
    attachmentClaimsHigherStackAlreadyCertified : Bool
    attachmentClaimsPhysicalLawAlreadyPromoted : Bool
    attachmentCollapsesIndependentTheoremOwnership : Bool

open NonginAttachedDescendantProgrammesBoundary public

canonicalNonginAttachedDescendantProgrammesBoundary :
  NonginAttachedDescendantProgrammesBoundary
canonicalNonginAttachedDescendantProgrammesBoundary =
  nongin-attached-descendant-programmes-boundary
    true true true true true true false false false

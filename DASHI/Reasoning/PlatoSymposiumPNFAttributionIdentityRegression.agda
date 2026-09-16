module DASHI.Reasoning.PlatoSymposiumPNFAttributionIdentityRegression where

import DASHI.Reasoning.PlatoSymposiumPNFAttributionIdentityExact as Bridge

------------------------------------------------------------------------
-- RED/GREEN regression surface for the JMD-owned Symposium PNF /
-- attribution / snowball / external-identity bridge.
--
-- The production owner must reuse canonical PNF, AttributedSourceCore,
-- snowball, Pareto and Dewey/QID/DOI identity machinery.  JMD archive theorem
-- contracts retain JMD ownership; DASHI owns only the new bridge theorems.
------------------------------------------------------------------------

pnfBoundaryPinned = Bridge.existingPNFBoundary
attributedSourceCorePinned = Bridge.existingAttributedSourceCoreReceipt
snowballBoundaryPinned = Bridge.existingAttributionSnowballBoundary
externalIdentityPolicyPinned = Bridge.existingExternalIdentityPolicy
symbolicIdentityBoundaryPinned = Bridge.existingDeweyQidDoiBoundary
wikidataPNFBoundaryPinned = Bridge.existingWikidataPNFBoundary
paretoBoundaryPinned = Bridge.existingRecursiveParetoBoundary
ownershipDeclarationPinned = Bridge.archiveOwnershipDeclaration

pnfShapeSourceRoleBoundary = Bridge.pnfShapeDoesNotDetermineSourceRole
identifierObligationBoundary = Bridge.identifierCompletenessDoesNotDetermineEvidenceObligationStatus

archiveDoiDemandPinned = Bridge.archiveDoiDemand
symposiumQidDemandPinned = Bridge.symposiumQidDemand
platoDeweyCoordinatePinned = Bridge.platoDeweyCoordinate

citationNotAuthority = Bridge.citationStillDoesNotCreateAuthority
qidNotTruth = Bridge.qidStillDoesNotPaySourceTruth
doiNotConceptIdentity = Bridge.doiStillDoesNotIdentifyConcept
propertyIdNotInferentialForce = Bridge.propertyIdStillDoesNotDetermineInferentialForce

canonicalBoundary = Bridge.canonicalPlatoSymposiumPNFAttributionIdentityBoundary

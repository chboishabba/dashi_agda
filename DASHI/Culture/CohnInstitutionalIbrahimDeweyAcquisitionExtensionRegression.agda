module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionExact as Acquisition
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

longinoAuthorPinned :
  Source.sourceAuthor Acquisition.longinoScienceAsSocialKnowledge ≡ "Helen E. Longino"
longinoAuthorPinned = refl

longinoDoiPinned :
  Source.doiState Acquisition.longinoScienceAsSocialKnowledge ≡
  Source.doiRecorded "10.2307/j.ctvx5wbfz"
longinoDoiPinned = refl

longinoAuthorQidPinned :
  Id.rawItemId Acquisition.helenLonginoAuthorQid ≡ "Q5702699"
longinoAuthorQidPinned = refl

dotsonAuthorPinned :
  Source.sourceAuthor Acquisition.dotsonTrackingEpistemicViolence ≡ "Kristie Dotson"
dotsonAuthorPinned = refl

dotsonDoiPinned :
  Source.doiState Acquisition.dotsonTrackingEpistemicViolence ≡
  Source.doiRecorded "10.1111/j.1527-2001.2011.01177.x"
dotsonDoiPinned = refl

medinaAuthorPinned :
  Source.sourceAuthor Acquisition.medinaPolyphonicContextualism ≡ "José Medina"
medinaAuthorPinned = refl

medinaDoiPinned :
  Source.doiState Acquisition.medinaPolyphonicContextualism ≡
  Source.doiRecorded "10.1080/02691728.2011.652214"
medinaDoiPinned = refl

longinoPublicationQidStillDebt :
  Acquisition.longinoPublicationQidResolved
    Acquisition.canonicalAcquisitionIdentifierBoundary ≡ false
longinoPublicationQidStillDebt = refl

dotsonPublicationQidStillDebt :
  Acquisition.dotsonPublicationQidResolved
    Acquisition.canonicalAcquisitionIdentifierBoundary ≡ false
dotsonPublicationQidStillDebt = refl

medinaPublicationQidStillDebt :
  Acquisition.medinaPublicationQidResolved
    Acquisition.canonicalAcquisitionIdentifierBoundary ≡ false
medinaPublicationQidStillDebt = refl

longinoSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Acquisition.longinoScienceAsSocialKnowledge
longinoSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Acquisition.longinoScienceAsSocialKnowledge

dotsonSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Acquisition.dotsonTrackingEpistemicViolence
dotsonSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Acquisition.dotsonTrackingEpistemicViolence

medinaSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Acquisition.medinaPolyphonicContextualism
medinaSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Acquisition.medinaPolyphonicContextualism

newSourceDoesNotOwnRepairTheorem :
  Acquisition.acquiredPrimarySourcesOwnDashiRepairTheorem
    Acquisition.canonicalAcquisitionAttributionBoundary ≡ false
newSourceDoesNotOwnRepairTheorem = refl

silencingDoesNotAutomaticallyProveInstitutionalOutcome :
  Acquisition.silencingSourceProvesSpecificInstitutionalOutcome
    Acquisition.canonicalAcquisitionAttributionBoundary ≡ false
silencingDoesNotAutomaticallyProveInstitutionalOutcome = refl

contextualEvidenceDoesNotCreateUniversalRelativism :
  Acquisition.contextualEvidenceMeansAnythingGoes
    Acquisition.canonicalAcquisitionAttributionBoundary ≡ false
contextualEvidenceDoesNotCreateUniversalRelativism = refl

longinoToEvidenceContextEdge : Ibrahim.DashiFirstLinkEdge
longinoToEvidenceContextEdge = Acquisition.longinoToEvidenceContext

dotsonToTestimonyUptakeEdge : Ibrahim.DashiFirstLinkEdge
dotsonToTestimonyUptakeEdge = Acquisition.dotsonToTestimonyUptake

medinaToInterpretiveResourcesEdge : Ibrahim.DashiFirstLinkEdge
medinaToInterpretiveResourcesEdge = Acquisition.medinaToInterpretiveResources

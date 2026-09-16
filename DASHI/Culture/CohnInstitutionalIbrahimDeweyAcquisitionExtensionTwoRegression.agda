module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionTwoRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionTwoExact as Acquisition
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

tuanaAuthorQidPinned :
  Id.rawItemId Acquisition.nancyTuanaAuthorQid ≡ "Q27451854"
tuanaAuthorQidPinned = refl

andersonAuthorQidPinned :
  Id.rawItemId Acquisition.elizabethAndersonAuthorQid ≡ "Q1331312"
andersonAuthorQidPinned = refl

tuanaAuthorPinned :
  Source.sourceAuthor Acquisition.tuanaComingToUnderstand ≡ "Nancy Tuana"
tuanaAuthorPinned = refl

pohlhausAuthorPinned :
  Source.sourceAuthor Acquisition.pohlhausWillfulHermeneuticalIgnorance ≡ "Gaile Pohlhaus Jr."
pohlhausAuthorPinned = refl

andersonAuthorPinned :
  Source.sourceAuthor Acquisition.andersonFeministEpistemology ≡ "Elizabeth Anderson"
andersonAuthorPinned = refl

tuanaDoiPinned :
  Source.doiState Acquisition.tuanaComingToUnderstand ≡
  Source.doiRecorded "10.1111/j.1527-2001.2004.tb01275.x"
tuanaDoiPinned = refl

pohlhausDoiPinned :
  Source.doiState Acquisition.pohlhausWillfulHermeneuticalIgnorance ≡
  Source.doiRecorded "10.1111/j.1527-2001.2011.01222.x"
pohlhausDoiPinned = refl

andersonDoiPinned :
  Source.doiState Acquisition.andersonFeministEpistemology ≡
  Source.doiRecorded "10.1111/j.1527-2001.1995.tb00737.x"
andersonDoiPinned = refl

tuanaSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Acquisition.tuanaComingToUnderstand
tuanaSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Acquisition.tuanaComingToUnderstand

pohlhausSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Acquisition.pohlhausWillfulHermeneuticalIgnorance
pohlhausSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Acquisition.pohlhausWillfulHermeneuticalIgnorance

andersonSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Acquisition.andersonFeministEpistemology
andersonSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Acquisition.andersonFeministEpistemology

tuanaPublicationQidStillDebt :
  Acquisition.tuanaPublicationQidResolved Acquisition.canonicalAcquisitionTwoIdentifierBoundary ≡ false
tuanaPublicationQidStillDebt = refl

pohlhausPersonQidStillDebt :
  Acquisition.pohlhausPersonQidResolved Acquisition.canonicalAcquisitionTwoIdentifierBoundary ≡ false
pohlhausPersonQidStillDebt = refl

andersonPublicationQidStillDebt :
  Acquisition.andersonPublicationQidResolved Acquisition.canonicalAcquisitionTwoIdentifierBoundary ≡ false
andersonPublicationQidStillDebt = refl

constructedIgnoranceIsNotMissingData :
  Acquisition.constructedIgnoranceEqualsSimpleMissingData
    Acquisition.canonicalAcquisitionTwoAttributionBoundary ≡ false
constructedIgnoranceIsNotMissingData = refl

willfulIgnoranceDoesNotProveBadFaith :
  Acquisition.willfulIgnoranceSourceProvesSpecificBadFaith
    Acquisition.canonicalAcquisitionTwoAttributionBoundary ≡ false
willfulIgnoranceDoesNotProveBadFaith = refl

feministEpistemologyDoesNotCreateAuthority :
  Acquisition.feministEpistemologyCreatesInstitutionalAuthority
    Acquisition.canonicalAcquisitionTwoAttributionBoundary ≡ false
feministEpistemologyDoesNotCreateAuthority = refl

acquisitionAddsCandidateFamilies :
  Acquisition.acquisitionAddsDistinctCandidateCoordinateFamilies
    Acquisition.canonicalAcquisitionTwoAttributionBoundary ≡ true
acquisitionAddsCandidateFamilies = refl

tuanaEdge : Ibrahim.DashiFirstLinkEdge
tuanaEdge = Acquisition.tuanaToIgnoranceProduction

pohlhausEdge : Ibrahim.DashiFirstLinkEdge
pohlhausEdge = Acquisition.pohlhausToHermeneuticalRefusal

andersonEdge : Ibrahim.DashiFirstLinkEdge
andersonEdge = Acquisition.andersonToCriticalUptake

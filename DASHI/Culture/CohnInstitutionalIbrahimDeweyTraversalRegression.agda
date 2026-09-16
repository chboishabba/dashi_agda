module DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

cohnPublicationQidPinned :
  Id.rawItemId Traversal.cohnSexAndDeathPublicationQid ≡ "Q104206590"
cohnPublicationQidPinned = refl

harawayPublicationQidPinned :
  Id.rawItemId Traversal.harawaySituatedKnowledgesPublicationQid ≡ "Q29014379"
harawayPublicationQidPinned = refl

harawayAuthorQidPinned :
  Id.rawItemId Traversal.donnaHarawayAuthorQid ≡ "Q253407"
harawayAuthorQidPinned = refl

blackwellAuthorQidPinned :
  Id.rawItemId Traversal.davidBlackwellAuthorQid ≡ "Q525037"
blackwellAuthorQidPinned = refl

frickerAuthorQidPinned :
  Id.rawItemId Traversal.mirandaFrickerAuthorQid ≡ "Q13522475"
frickerAuthorQidPinned = refl

epistemicInjusticeConceptQidPinned :
  Id.rawItemId Traversal.epistemicInjusticeConceptQid ≡ "Q48970669"
epistemicInjusticeConceptQidPinned = refl

harawayAuthorPinned :
  Source.sourceAuthor Traversal.harawaySituatedKnowledges ≡ "Donna Haraway"
harawayAuthorPinned = refl

blackwellAuthorPinned :
  Source.sourceAuthor Traversal.blackwellEquivalentComparisons ≡ "David Blackwell"
blackwellAuthorPinned = refl

frickerAuthorPinned :
  Source.sourceAuthor Traversal.frickerEpistemicInjustice ≡ "Miranda Fricker"
frickerAuthorPinned = refl

harawayDoiPinned :
  Source.doiState Traversal.harawaySituatedKnowledges ≡
  Source.doiRecorded "10.2307/3178066"
harawayDoiPinned = refl

blackwellDoiPinned :
  Source.doiState Traversal.blackwellEquivalentComparisons ≡
  Source.doiRecorded "10.1214/aoms/1177729032"
blackwellDoiPinned = refl

frickerDoiPinned :
  Source.doiState Traversal.frickerEpistemicInjustice ≡
  Source.doiRecorded "10.1093/acprof:oso/9780198237907.001.0001"
frickerDoiPinned = refl

harawaySnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Traversal.harawaySituatedKnowledges
harawaySnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Traversal.harawaySituatedKnowledges

blackwellSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Traversal.blackwellEquivalentComparisons
blackwellSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Traversal.blackwellEquivalentComparisons

frickerSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt Traversal.frickerEpistemicInjustice
frickerSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt Traversal.frickerEpistemicInjustice

blackwellPublicationQidStillDebt :
  Traversal.blackwellPublicationQidResolved
    Traversal.canonicalTraversalIdentifierBoundary ≡ false
blackwellPublicationQidStillDebt = refl

frickerPublicationQidStillDebt :
  Traversal.frickerPublicationQidResolved
    Traversal.canonicalTraversalIdentifierBoundary ≡ false
frickerPublicationQidStillDebt = refl

publicationQidDoesNotBecomeAuthorQid :
  Traversal.publicationQidEqualsAuthorQid
    Traversal.canonicalTraversalIdentifierBoundary ≡ false
publicationQidDoesNotBecomeAuthorQid = refl

deweyIsNavigationOnly :
  Traversal.deweyParentCreatesTheoremEdge
    Traversal.canonicalTraversalAttributionBoundary ≡ false
deweyIsNavigationOnly = refl

qidIsNavigationOnly :
  Traversal.qidCreatesProof
    Traversal.canonicalTraversalAttributionBoundary ≡ false
qidIsNavigationOnly = refl

doiIsBibliographicIdentityOnly :
  Traversal.doiCreatesDASHITheorem
    Traversal.canonicalTraversalAttributionBoundary ≡ false
doiIsBibliographicIdentityOnly = refl

sourceCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority Traversal.harawaySituatedKnowledges ≡ false
sourceCitationDoesNotCreateAuthority = refl

blackwellSourceDoesNotOwnRepairTheorem :
  Traversal.externalSourceOwnsLeastCoordinateRepair
    Traversal.canonicalTraversalAttributionBoundary ≡ false
blackwellSourceDoesNotOwnRepairTheorem = refl

highestAlphaFrontierRemainsTyped :
  Traversal.traversalHighestAlphaFrontierIsTypedDependency
    Traversal.canonicalTraversalAttributionBoundary ≡ true
highestAlphaFrontierRemainsTyped = refl

cohnToSituatedKnowledgeEdge : Ibrahim.DashiFirstLinkEdge
cohnToSituatedKnowledgeEdge = Traversal.cohnToSituatedKnowledge

blackwellToRepairEdge : Ibrahim.DashiFirstLinkEdge
blackwellToRepairEdge = Traversal.blackwellToLeastCoordinateRepair

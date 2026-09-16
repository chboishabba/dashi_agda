module DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Core.AttributedSourceCore as Source
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

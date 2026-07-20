module DASHI.Governance.ArtifactAuthorityPromotionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.GovernedArtifactCore as Governed
import DASHI.Governance.PromotionSpine as Spine

------------------------------------------------------------------------
-- Citation authority and artifact authority feed different promotion slots.
--
-- A citation-only boundary can identify a source while still failing the
-- canonical-artifact identity gate.  Conversely, artifact promotion requires
-- accepted artifact authority and a materialized machine-readable artifact,
-- plus the four independent closure obligations owned by the canonical kernel.

artifactIdentityGate :
  Bool →
  Bool →
  Bool →
  Bool
artifactIdentityGate false machineReadable accepted =
  false
artifactIdentityGate true false accepted =
  false
artifactIdentityGate true true false =
  false
artifactIdentityGate true true true =
  true

authorityIdentityClosed :
  ∀ {kind : Authority.AuthorityKind} →
  Authority.AuthorityBoundary kind →
  Bool
authorityIdentityClosed boundary =
  artifactIdentityGate
    (Authority.artifactAuthority boundary)
    (Authority.machineReadableArtifactPresent boundary)
    (Authority.authorityAccepted boundary)

authorityPromotionObligations :
  ∀ {kind : Authority.AuthorityKind} →
  Authority.AuthorityBoundary kind →
  Bool →
  Bool →
  Bool →
  Bool →
  Canonical.PromotionObligations
authorityPromotionObligations
  boundary
  admissibility
  residualClosure
  witnessClosure
  validationClosure =
  Canonical.promotionObligations
    (authorityIdentityClosed boundary)
    admissibility
    residualClosure
    witnessClosure
    validationClosure

record ArtifactAuthorityClosure
  (boundary : Authority.ArtifactAuthorityBoundary) :
  Set where
  constructor artifactAuthorityClosure
  field
    authorityAcceptedIsTrue :
      Authority.authorityAccepted boundary ≡ true

    artifactAuthorityIsTrue :
      Authority.artifactAuthority boundary ≡ true

    machineReadableArtifactPresentIsTrue :
      Authority.machineReadableArtifactPresent boundary ≡ true

open ArtifactAuthorityClosure public

artifactAuthorityClosesIdentity :
  ∀ {boundary : Authority.ArtifactAuthorityBoundary} →
  ArtifactAuthorityClosure boundary →
  authorityIdentityClosed boundary ≡ true
artifactAuthorityClosesIdentity {boundary} closure
  rewrite artifactAuthorityIsTrue closure
        | machineReadableArtifactPresentIsTrue closure
        | authorityAcceptedIsTrue closure =
  refl

artifactAuthorityPromotesWhenRemainingClosed :
  ∀ {boundary : Authority.ArtifactAuthorityBoundary} →
  ArtifactAuthorityClosure boundary →
  Canonical.promote
    (authorityPromotionObligations boundary true true true true)
    ≡ Canonical.promoted
artifactAuthorityPromotesWhenRemainingClosed {boundary} closure
  rewrite artifactAuthorityClosesIdentity closure =
  refl

artifactAuthorityAuthorizesGovernedPromotion :
  ∀ {boundary : Authority.ArtifactAuthorityBoundary} →
  ArtifactAuthorityClosure boundary →
  Spine.authorizationFromObligations
    (authorityPromotionObligations boundary true true true true)
    ≡ Governed.promote
artifactAuthorityAuthorizesGovernedPromotion {boundary} closure
  rewrite artifactAuthorityClosesIdentity closure =
  refl

citationOnlyCannotCloseArtifactIdentity :
  (evidence : Authority.CitationAuthorityNoArtifact) →
  authorityIdentityClosed (Authority.citationBoundary evidence)
    ≡ false
citationOnlyCannotCloseArtifactIdentity evidence
  rewrite Authority.artifactAuthorityIsFalse evidence =
  refl

citationOnlyQuarantines :
  (evidence : Authority.CitationAuthorityNoArtifact) →
  (admissibility residualClosure witnessClosure validationClosure : Bool) →
  Canonical.promote
    (authorityPromotionObligations
      (Authority.citationBoundary evidence)
      admissibility
      residualClosure
      witnessClosure
      validationClosure)
    ≡ Canonical.quarantinedStatus
citationOnlyQuarantines
  evidence
  admissibility
  residualClosure
  witnessClosure
  validationClosure
  rewrite citationOnlyCannotCloseArtifactIdentity evidence =
  refl

citationOnlyAuthorizationAbstains :
  (evidence : Authority.CitationAuthorityNoArtifact) →
  (admissibility residualClosure witnessClosure validationClosure : Bool) →
  Spine.authorizationFromObligations
    (authorityPromotionObligations
      (Authority.citationBoundary evidence)
      admissibility
      residualClosure
      witnessClosure
      validationClosure)
    ≡ Governed.abstain
citationOnlyAuthorizationAbstains
  evidence
  admissibility
  residualClosure
  witnessClosure
  validationClosure
  rewrite citationOnlyCannotCloseArtifactIdentity evidence =
  refl

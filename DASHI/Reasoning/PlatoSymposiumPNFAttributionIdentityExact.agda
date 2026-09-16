module DASHI.Reasoning.PlatoSymposiumPNFAttributionIdentityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.RecursiveParetoFrontierLiftingExact as Pareto
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source
import DASHI.Reasoning.PlatoSymposiumResidualDialecticMechanismExact as Residual
import DASHI.Reasoning.PlatoSymposiumSnowballParetoIndexingExact as Indexing
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as DeweyQidDoi
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.WikidataPNFPredicateBridgeExact as WikidataPNF

------------------------------------------------------------------------
-- JMD SYMPOSIUM / PNF / ATTRIBUTION / EXTERNAL-IDENTITY BRIDGE
--
-- This is a thin adapter over existing repository owners.
--
-- Attribution rule:
--   all theorem contracts and source artifacts imported from the supplied
--   c56a9d2-output-20260916.tar.gz archive remain attributed to James Michael
--   DuPont (JMD / meta-introspector).  DASHI owns only the finite bridge
--   theorems introduced here.  PNF normalisation, Dewey/QID/DOI coordinates,
--   snowball position and Pareto position do not transfer source ownership.
--
-- PNF rule:
--   Predicate Normal Form exposes quantifier, scope, predicate and inferential
--   obligations.  It does not identify who owns the source theorem or whether
--   each evidence obligation has been discharged.
--
-- Identity rule:
--   DOI is publication/source identity, QID is entity/concept identity and
--   Dewey is classification/navigation.  Missing identifiers remain explicit;
--   they are not invented and do not normally block an unrelated domain proof.
------------------------------------------------------------------------

archiveOwnershipDeclaration : Source.OwnershipDeclaration
archiveOwnershipDeclaration = Source.jmdOwnershipDeclaration

jmdBundleSource : Attribution.AttributedSource
jmdBundleSource = Source.jmdBundleSource

jmdMarsyasContract = Residual.marsyasSameEffectDifferentMeansContract
jmdEryximachusContract = Residual.eryximachusHostileReconcilableContract

------------------------------------------------------------------------
-- Canonical parents remain authoritative.
------------------------------------------------------------------------

existingPNFBoundary : PNF.PredicateNormalFormBoundary
existingPNFBoundary = PNF.canonicalPredicateNormalFormBoundary

existingAttributedSourceCoreReceipt = Attribution.canonicalAttributedSourceCoreReceipt

existingAttributionSnowballBoundary : Snowball.AttributionSnowballBoundary
existingAttributionSnowballBoundary = Snowball.canonicalAttributionSnowballBoundary

existingExternalIdentityPolicy : Identity.SnowballExternalIdentityPolicy
existingExternalIdentityPolicy = Identity.canonicalExternalIdentityPolicy

existingDeweyQidDoiBoundary : DeweyQidDoi.SymbolicVerificationDeweyQidDoiBoundary
existingDeweyQidDoiBoundary = DeweyQidDoi.canonicalSymbolicVerificationDeweyQidDoiBoundary

existingWikidataPNFBoundary : WikidataPNF.WikidataPNFBoundary
existingWikidataPNFBoundary = WikidataPNF.canonicalWikidataPNFBoundary

existingRecursiveParetoBoundary : Pareto.RecursiveParetoFrontierBoundary
existingRecursiveParetoBoundary = Pareto.canonicalRecursiveParetoFrontierBoundary

platoDeweyCoordinate = Indexing.platoPhilosophyCoordinate

------------------------------------------------------------------------
-- External identity demands: retain absence/unresolved state explicitly.
------------------------------------------------------------------------

archiveDoiDemand : Identity.ExternalIdentityDemand
archiveDoiDemand = Identity.mkOptionalIdentityDemand
  "JMD Symposium PNF attribution bridge"
  "retain publication/source identity without inventing identifiers"
  "JMD Aristotle Symposium / Republic attached source archive"
  Identity.doi
  (Identity.notApplicable
    "the supplied attachment is the JMD source artifact; no DOI was supplied or asserted for the archive")

symposiumQidDemand : Identity.ExternalIdentityDemand
symposiumQidDemand = Identity.mkOptionalIdentityDemand
  "JMD Symposium PNF attribution bridge"
  "same-object external identity must be verified before recording"
  "Plato Symposium work/source identity relevant to this bridge"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact QID promoted by this tranche; retain unresolved until same-object verification is paid")

archiveDoiStateIsAtlasLocalAbsence :
  Attribution.doiState jmdBundleSource ≡ Attribution.noDOIRecordedByAtlas
archiveDoiStateIsAtlasLocalAbsence = refl

------------------------------------------------------------------------
-- Concrete PNF surface for a bridge-level claim.
--
-- The same PNF assertion can occur once as a source-facing theorem reading and
-- once as a DASHI-owned structural bridge result.  PNF shape therefore cannot
-- determine source/ownership role.
------------------------------------------------------------------------

sharedMechanismScope : PNF.AssertionScope
sharedMechanismScope = PNF.assertionScope
  "two source-defined agents/cases"
  "declared comparison context"
  "observe common effect"
  "compare operative means"
  "means/mechanism distinction"
  "source-bounded / no temporal generalisation"

sharedMechanismPredicates =
  PNF.predicateAtom
    "same-observed-effect"
    PNF.outcomePredicate
    "case × effect × context"
    "the compared cases expose the same selected effect surface"
  ∷ PNF.predicateAtom
    "operative-means"
    PNF.comparatorPredicate
    "case × means × context"
    "the compared cases may realise that effect through different means"
  ∷ []

sharedMechanismPNF : PNF.PredicateNormalAssertion
sharedMechanismPNF = PNF.predicateNormalAssertion
  "plato-symposium-effect-means-bridge"
  "The same observed effect does not by itself determine the operative means."
  PNF.boundedUniversalQ
  PNF.comparativeF
  sharedMechanismScope
  sharedMechanismPredicates
  "JMD Marsyas theorem is the source fixture; the non-factorability theorem is DASHI-owned"

------------------------------------------------------------------------
-- 1. PNF shape does not determine source/ownership role.
------------------------------------------------------------------------

data PNFRoleWorld : Set where
  jmdSourceTheoremWorld : PNFRoleWorld
  dashiBridgeTheoremWorld : PNFRoleWorld

data SourceRoleQuery : Set where
  sourceRoleQuestion : SourceRoleQuery

data SourceRoleAnswer : Set where
  jmdOwnedArchiveTheorem : SourceRoleAnswer
  dashiOwnedBridgeTheorem : SourceRoleAnswer

pnfShapeProjection : PNFRoleWorld → PNF.PredicateNormalAssertion
pnfShapeProjection jmdSourceTheoremWorld = sharedMechanismPNF
pnfShapeProjection dashiBridgeTheoremWorld = sharedMechanismPNF

SourceRoleAnswerFor : SourceRoleQuery → Set
SourceRoleAnswerFor sourceRoleQuestion = SourceRoleAnswer

askSourceRole :
  (query : SourceRoleQuery) → PNFRoleWorld → SourceRoleAnswerFor query
askSourceRole sourceRoleQuestion jmdSourceTheoremWorld = jmdOwnedArchiveTheorem
askSourceRole sourceRoleQuestion dashiBridgeTheoremWorld = dashiOwnedBridgeTheorem

sourceRoleQuestions : Query.InquiryQuestionFamily PNFRoleWorld SourceRoleQuery
sourceRoleQuestions = Query.inquiryQuestionFamily SourceRoleAnswerFor askSourceRole

pnfShapeDoesNotDetermineSourceRole :
  Query.FactorsThrough sourceRoleQuestions pnfShapeProjection sourceRoleQuestion → ⊥
pnfShapeDoesNotDetermineSourceRole factor = helper first second
  where
    first :
      jmdOwnedArchiveTheorem ≡ Query.quotientAnswer factor sharedMechanismPNF
    first = Query.factorisation factor jmdSourceTheoremWorld

    second :
      dashiOwnedBridgeTheorem ≡ Query.quotientAnswer factor sharedMechanismPNF
    second = Query.factorisation factor dashiBridgeTheoremWorld

    helper :
      jmdOwnedArchiveTheorem ≡ Query.quotientAnswer factor sharedMechanismPNF →
      dashiOwnedBridgeTheorem ≡ Query.quotientAnswer factor sharedMechanismPNF → ⊥
    helper refl ()

------------------------------------------------------------------------
-- 2. Complete-looking identity metadata does not discharge PNF obligations.
------------------------------------------------------------------------

data IdentityAuditWorld : Set where
  completeIdentifiersPaidObligation : IdentityAuditWorld
  completeIdentifiersOpenObligation : IdentityAuditWorld

data IdentifierSurface : Set where
  deweyQidDoiPresent : IdentifierSurface

data EvidenceObligationQuery : Set where
  evidenceObligationStatusQuestion : EvidenceObligationQuery

identifierProjection : IdentityAuditWorld → IdentifierSurface
identifierProjection completeIdentifiersPaidObligation = deweyQidDoiPresent
identifierProjection completeIdentifiersOpenObligation = deweyQidDoiPresent

EvidenceObligationAnswerFor : EvidenceObligationQuery → Set
EvidenceObligationAnswerFor evidenceObligationStatusQuestion = PNF.ObligationStatus

askEvidenceObligation :
  (query : EvidenceObligationQuery) →
  IdentityAuditWorld →
  EvidenceObligationAnswerFor query
askEvidenceObligation evidenceObligationStatusQuestion completeIdentifiersPaidObligation =
  PNF.discharged
askEvidenceObligation evidenceObligationStatusQuestion completeIdentifiersOpenObligation =
  PNF.unresolved

evidenceObligationQuestions :
  Query.InquiryQuestionFamily IdentityAuditWorld EvidenceObligationQuery
evidenceObligationQuestions =
  Query.inquiryQuestionFamily EvidenceObligationAnswerFor askEvidenceObligation

identifierCompletenessDoesNotDetermineEvidenceObligationStatus :
  Query.FactorsThrough
    evidenceObligationQuestions
    identifierProjection
    evidenceObligationStatusQuestion → ⊥
identifierCompletenessDoesNotDetermineEvidenceObligationStatus factor = helper first second
  where
    first :
      PNF.discharged ≡ Query.quotientAnswer factor deweyQidDoiPresent
    first = Query.factorisation factor completeIdentifiersPaidObligation

    second :
      PNF.unresolved ≡ Query.quotientAnswer factor deweyQidDoiPresent
    second = Query.factorisation factor completeIdentifiersOpenObligation

    helper :
      PNF.discharged ≡ Query.quotientAnswer factor deweyQidDoiPresent →
      PNF.unresolved ≡ Query.quotientAnswer factor deweyQidDoiPresent → ⊥
    helper refl ()

------------------------------------------------------------------------
-- Existing firewalls pinned directly.
------------------------------------------------------------------------

citationStillDoesNotCreateAuthority : Snowball.CitationCreatesDomainAuthority → ⊥
citationStillDoesNotCreateAuthority = Snowball.citationDoesNotCreateAuthority

qidStillDoesNotPaySourceTruth : Identity.QidPaysSourceTruth → ⊥
qidStillDoesNotPaySourceTruth = Identity.qidDoesNotPaySourceTruth

doiStillDoesNotIdentifyConcept : DeweyQidDoi.DOIIdentifiesConcept → ⊥
doiStillDoesNotIdentifyConcept = DeweyQidDoi.doiDoesNotIdentifyConcept

propertyIdStillDoesNotDetermineInferentialForce :
  WikidataPNF.PropertyIdDeterminesInferentialForce → ⊥
propertyIdStillDoesNotDetermineInferentialForce =
  WikidataPNF.propertyIdDoesNotDetermineInferentialForce

citationPresenceStillDoesNotDischargeEveryPredicate :
  PNF.citationPresenceDischargesEveryPredicate PNF.canonicalPredicateNormalFormBoundary ≡ false
citationPresenceStillDoesNotDischargeEveryPredicate = refl

strongerClaimStillNeedsNewReceipt :
  PNF.strongerDownstreamClaimNeedsNewEvidenceReceipt PNF.canonicalPredicateNormalFormBoundary ≡ true
strongerClaimStillNeedsNewReceipt = refl

unresolvedIdentityStillNotNegativeEvidence :
  Identity.unresolvedIdentityIsNegativeEvidence Identity.canonicalExternalIdentityPolicy ≡ false
unresolvedIdentityStillNotNegativeEvidence = refl

paretoStillDoesNotCreateProofAuthority :
  Pareto.paretoFrontierRefinementCreatesProofAuthority
    Pareto.canonicalRecursiveParetoFrontierBoundary ≡ false
paretoStillDoesNotCreateProofAuthority = refl

------------------------------------------------------------------------
-- Authority / attribution boundary.
------------------------------------------------------------------------

record PlatoSymposiumPNFAttributionIdentityBoundary : Set where
  constructor plato-symposium-pnf-attribution-identity-boundary
  field
    allArchiveSourceMaterialRetainsJMDAttribution : Bool
    pnfNormalisationTransfersSourceOwnership : Bool
    pnfShapeDeterminesSourceRole : Bool
    completeIdentifiersDischargeEveryEvidenceObligation : Bool
    doiCreatesClaimSemantics : Bool
    qidCreatesTruth : Bool
    deweyCreatesTruth : Bool
    unresolvedIdentityIsNegativeEvidence : Bool
    missingArchiveDoiMayBeInvented : Bool
    pnfPromotionStillRequiresEvidenceReceipt : Bool
    paretoPositionCreatesProofAuthority : Bool
    canonicalOwnersRemainAuthoritative : Bool

open PlatoSymposiumPNFAttributionIdentityBoundary public

canonicalPlatoSymposiumPNFAttributionIdentityBoundary :
  PlatoSymposiumPNFAttributionIdentityBoundary
canonicalPlatoSymposiumPNFAttributionIdentityBoundary =
  plato-symposium-pnf-attribution-identity-boundary
    true
    false
    false
    false
    false
    false
    false
    false
    false
    true
    false
    true

pnfAttributionIdentitySummary : String
pnfAttributionIdentitySummary =
  "All supplied archive source material remains JMD-attributed. Predicate Normal Form exposes claim obligations but does not determine source ownership; Dewey, QID and DOI remain classification/entity/source-identity coordinates and do not discharge scope, causal, transport, normative or authority obligations. Missing identifiers remain explicit rather than invented, and Pareto position does not create proof authority."

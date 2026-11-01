module DASHI.Policy.ABC730IbrahimSnowballAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Wiki
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact as Speaker
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Consequence
import DASHI.Policy.AustraliaIsraelSanctionsAttributionExact as Attribution

------------------------------------------------------------------------
-- ABC 7.30 Ibrahim / Snowball attribution overlay.
--
-- Coordinates are deliberately orthogonal:
--   Dewey = where in subject space;
--   QID = external entity identity;
--   DOI/stable source ID = which source object;
--   primaryness = what claim-role the object is primary for;
--   DASHI owner = which formalisation consumes it.
-- None of those coordinates imports truth or authority into another.
------------------------------------------------------------------------

data QidState : Set where
  verifiedQid : String → QidState
  unresolvedQid : String → QidState

data StableIdentifier : Set where
  doiIdentifier : String → StableIdentifier
  urlSha256Identifier : String → String → StableIdentifier

data ClaimRelativeSourceRole : Set where
  primarySpeakerLabel : ClaimRelativeSourceRole
  primaryUtteranceWording : ClaimRelativeSourceRole
  primaryStatedPolicyPosition : ClaimRelativeSourceRole
  primaryInterviewQuestion : ClaimRelativeSourceRole
  secondaryReportedWorldEvent : ClaimRelativeSourceRole
  secondaryIndependentLegalTruth : ClaimRelativeSourceRole
  secondaryCausalEffectiveness : ClaimRelativeSourceRole

data SnowballPaymentState : Set where
  acquiredRetained : SnowballPaymentState
  sourceIdentityPaid : SnowballPaymentState
  entityIdentityPaid : SnowballPaymentState
  claimRolePaid : SnowballPaymentState
  unresolvedPayment : SnowballPaymentState

record IbrahimSourceCoordinate : Set where
  constructor ibrahimSourceCoordinate
  field
    sourceReference : String
    attributedSource : Source.AttributedSource
    deweyParent : String
    stableIdentifier : StableIdentifier
    programmeQid : QidState
    publisherQid : QidState
    sourceRoleReference : String
    transcriptSha256 : String
    pageSha256 : String
    deweyCreatesAuthority : Bool
    qidCreatesAuthority : Bool
    primarynessCreatesWorldTruth : Bool

open IbrahimSourceCoordinate public

abcAttributedSource : Source.AttributedSource
abcAttributedSource = Source.mkNoDOISource
  "ABC News / 7.30 editorial production"
  "New sanctions placed on Israeli settlements"
  "ABC News / 7.30"
  "2026"
  "https://www.abc.net.au/news/2026-09-09/new-sanctions-placed-on-israeli-settlements-/107135268"
  Source.newsSource
  "speaker-labelled broadcast transcript; primary for speaker labels/utterance wording/stated policy positions, not automatically primary for underlying world claims"
  Source.publicAttribution

abcPrimaryCoordinate : IbrahimSourceCoordinate
abcPrimaryCoordinate = ibrahimSourceCoordinate
  "abc730-2026-09-09:61c86754d9cb2ca6e540d522ebfa8056a42291afa257dd6c7e54f12374408383"
  abcAttributedSource
  "327"
  (urlSha256Identifier
    "https://www.abc.net.au/news/2026-09-09/new-sanctions-placed-on-israeli-settlements-/107135268"
    "61c86754d9cb2ca6e540d522ebfa8056a42291afa257dd6c7e54f12374408383")
  (verifiedQid "Q4642897")
  (verifiedQid "Q781365")
  "claim-relative primary programme transcript"
  "61c86754d9cb2ca6e540d522ebfa8056a42291afa257dd6c7e54f12374408383"
  "c6fbd6dfe5c24769c7f33ba8a98b16ebf1f1d1414daf7c3500d94554fca564e4"
  false false false

------------------------------------------------------------------------
-- Verified QID atlas for identities actually used by this policy lane.
------------------------------------------------------------------------

record PersonIdentityCoordinate : Set where
  constructor personIdentityCoordinate
  field
    sourceLabel : String
    qidState : QidState
    sourceObjectReference : String
    samePersonWeldReference : String
    qidPaysUtteranceTruth : Bool

open PersonIdentityCoordinate public

pennyWongIdentity : PersonIdentityCoordinate
pennyWongIdentity = personIdentityCoordinate
  "Penny Wong" (verifiedQid "Q456759")
  "ABC730 primary transcript paragraph 21 / C028-C029"
  "speaker label + Wikidata person identity match"
  false

edHusicIdentity : PersonIdentityCoordinate
edHusicIdentity = personIdentityCoordinate
  "Ed Husic" (verifiedQid "Q5334974")
  "ABC730 primary transcript paragraph 23 / C030-C031"
  "speaker label + Wikidata person identity match"
  false

davidShoebridgeIdentity : PersonIdentityCoordinate
davidShoebridgeIdentity = personIdentityCoordinate
  "David Shoebridge" (verifiedQid "Q5239754")
  "ABC730 primary transcript paragraph 24 / C032"
  "speaker label + Wikidata person identity match"
  false

julianLeeserIdentity : PersonIdentityCoordinate
julianLeeserIdentity = personIdentityCoordinate
  "Julian Leeser" (verifiedQid "Q24191457")
  "ABC730 primary transcript paragraph 25 / C033"
  "speaker label + Wikidata person identity match"
  false

emilyThornberryIdentity : PersonIdentityCoordinate
emilyThornberryIdentity = personIdentityCoordinate
  "Emily Thornberry" (verifiedQid "Q272408")
  "ABC730 primary transcript interview package"
  "speaker label + Wikidata person identity match"
  false

sarahFergusonIdentity : PersonIdentityCoordinate
sarahFergusonIdentity = personIdentityCoordinate
  "Sarah Ferguson" (verifiedQid "Q17004206")
  "ABC730 primary transcript interviewer labels"
  "speaker label + Wikidata journalist identity match"
  false

jacobGreberIdentity : PersonIdentityCoordinate
jacobGreberIdentity = personIdentityCoordinate
  "Jacob Greber" (unresolvedQid "no verified QID paid in this atlas")
  "ABC730 primary transcript reporter label"
  "source label retained; QID intentionally unresolved"
  false

identityAtlas : List PersonIdentityCoordinate
identityAtlas =
  pennyWongIdentity ∷ edHusicIdentity ∷ davidShoebridgeIdentity ∷
  julianLeeserIdentity ∷ emilyThornberryIdentity ∷ sarahFergusonIdentity ∷
  jacobGreberIdentity ∷ []

------------------------------------------------------------------------
-- Claim-relative primaryness.  The same source can be primary for an utterance
-- while secondary for the world proposition mentioned inside that utterance.
------------------------------------------------------------------------

record ClaimRoleReceipt : Set where
  constructor claimRoleReceipt
  field
    claimReference : String
    role : ClaimRelativeSourceRole
    paymentState : SnowballPaymentState
    rationale : String

open ClaimRoleReceipt public

c029Role : ClaimRoleReceipt
c029Role = claimRoleReceipt
  "ABC730-2026-09-09-C029"
  primaryStatedPolicyPosition
  claimRolePaid
  "Primary for Wong's stated implementation/unintended-consequence rationale; not primary evidence that the predicted consequences actually occur."

c032Role : ClaimRoleReceipt
c032Role = claimRoleReceipt
  "ABC730-2026-09-09-C032"
  primaryUtteranceWording
  claimRolePaid
  "Primary for Shoebridge's exact evaluative utterance and speaker label; not proof that the evaluation is correct."

reportedEventRole : ClaimRoleReceipt
reportedEventRole = claimRoleReceipt
  "ABC730 reported West Bank events"
  secondaryReportedWorldEvent
  acquiredRetained
  "Reporter narration is retained as source evidence but underlying event truth requires event-level primary or independently corroborating receipts."

legalTruthRole : ClaimRoleReceipt
legalTruthRole = claimRoleReceipt
  "ABC730 legal characterisations"
  secondaryIndependentLegalTruth
  acquiredRetained
  "Statements of legal position are primary for the speaker/government position but do not independently pay legal truth."

------------------------------------------------------------------------
-- Ibrahim coordinates and typed explanatory edges.
------------------------------------------------------------------------

sourceNode : Ibrahim.DashiKnowledgeCoordinate
sourceNode = Ibrahim.dashi-knowledge-coordinate
  "tools/slr-discourse-reconstruct/specimens/abc730-2026-09-09-primary/source.txt"
  "DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact"
  "327"
  "Q4642897"
  "abc730-2026-09-09:61c86754d9cb2ca6e540d522ebfa8056a42291afa257dd6c7e54f12374408383"

consequenceNode : Ibrahim.DashiKnowledgeCoordinate
consequenceNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Policy/ABC730UnintendedConsequencesEvidenceObligationExact.agda"
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "327"
  "Q456759"
  "ABC730-2026-09-09-C029"

attributionNode : Ibrahim.DashiKnowledgeCoordinate
attributionNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Policy/AustraliaIsraelSanctionsAttributionExact.agda"
  "DASHI.Policy.AustraliaIsraelSanctionsAttributionExact"
  "327"
  "Q5239754"
  "ABC730-2026-09-09-C032"

consequenceSupportedBySource : Ibrahim.DashiFirstLinkEdge
consequenceSupportedBySource = Ibrahim.dashi-first-link-edge
  consequenceNode sourceNode Ibrahim.supportedBy Ibrahim.canonicalDashiFirstLinkPolicy
  "C029 is paid as a source-level statement of Wong's rationale by the same-object ABC transcript."
  true

attributionSupportedBySource : Ibrahim.DashiFirstLinkEdge
attributionSupportedBySource = Ibrahim.dashi-first-link-edge
  attributionNode sourceNode Ibrahim.supportedBy Ibrahim.canonicalDashiFirstLinkPolicy
  "C032 speaker/wording attribution is paid by the speaker-labelled ABC transcript."
  true

consequenceExternallyIdentifiedByWong : Ibrahim.DashiFirstLinkEdge
consequenceExternallyIdentifiedByWong = Ibrahim.dashi-first-link-edge
  consequenceNode sourceNode Ibrahim.externallyIdentifiedBy Ibrahim.canonicalDashiFirstLinkPolicy
  "Wong Q456759 is an external identity coordinate only; the QID does not pay the policy-effect mechanism."
  true

------------------------------------------------------------------------
-- Snowball acquisition/payment discipline.
------------------------------------------------------------------------

record SnowballAttributionBoundary : Set where
  constructor snowballAttributionBoundary
  field
    acquisitionMayBeOutOfDependencyOrder : Bool
    paymentMaySkipSameObjectWeld : Bool
    paymentMaySkipClaimRoleWeld : Bool
    qidMayReplaceSourceInspection : Bool
    deweyMayCreateSemanticEdge : Bool
    missingDoiMayBeInvented : Bool
    primaryForUtteranceMeansPrimaryForWorldTruth : Bool
    laterSourceMayRewriteEarlierUnresolvedState : Bool

canonicalSnowballAttributionBoundary : SnowballAttributionBoundary
canonicalSnowballAttributionBoundary =
  snowballAttributionBoundary true false false false false false false false

attributedSourceBoundary : Source.AttributedSource
attributedSourceBoundary = abcAttributedSource

identifierBoundary : Wiki.IdentifierBoundary
identifierBoundary = Wiki.canonicalIdentifierBoundary

ibrahimBoundary : Ibrahim.DashiKnowledgeTraversalBoundary
ibrahimBoundary = Ibrahim.canonicalDashiKnowledgeTraversalBoundary

speakerResolutionReference : String
speakerResolutionReference = "DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact"

consequenceObligationReference : String
consequenceObligationReference = "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"

attributionReference : String
attributionReference = "DASHI.Policy.AustraliaIsraelSanctionsAttributionExact"

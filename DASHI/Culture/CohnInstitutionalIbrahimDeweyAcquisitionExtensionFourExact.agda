module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFourExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact as Prior
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Wikimedia.IbrahimSnowballMandelaReligionIndigenousMemoryBraidingBidiExact as IndigenousFollow

------------------------------------------------------------------------
-- FOURTH IBRAHIM / QID / DEWEY ACQUISITION EXTENSION
--
-- This is a literal follow from extension three rather than a fresh theory
-- layer. Pareto rule:
--
--   * add Medina 2023 because collective epistemic activism / protest uptake is
--     a distinct communicative-resistance coordinate, not merely another label
--     for testimony non-uptake or individual hermeneutical refusal;
--   * add Young because formal access to deliberation and effective influence
--     inside deliberation are distinct, sharpening the "who is at the table"
--     frontier beyond participation-power alone;
--   * DO NOT reacquire Bartlett-Marshall-Marshall 2012. The canonical Ibrahim
--     snowball lane already owns its DOI/source object, traditional-knowledge
--     QIDs and fail-closed Two-Eyed concept/Dewey boundary. Reuse it directly.
--
-- These sources remain candidate-coordinate donors only. They do not prove a
-- Cohn fixture, select a repair, create authority, or establish bad faith.
------------------------------------------------------------------------

medinaEpistemologyOfProtest : Source.AttributedSource
medinaEpistemologyOfProtest = Source.mkDOISource
  "José Medina"
  "The Epistemology of Protest: Silencing, Epistemic Activism, and the Communicative Life of Resistance"
  "Oxford University Press"
  "2023"
  "10.1093/oso/9780197660904.001.0001"
  "https://doi.org/10.1093/oso/9780197660904.001.0001"
  Source.academicBookSource
  "Primary conceptual source for protest as communicative and epistemic resistance, including proper uptake, epistemic activism, public formation and transformation of social sensibilities. It motivates an epistemic-activism / resistant-uptake coordinate distinct from support count, individual testimony uptake and hermeneutical refusal. It does not make protest into proof or establish the truth of any protested claim."
  Source.publicAttribution

youngInclusionAndDemocracy : Source.AttributedSource
youngInclusionAndDemocracy = Source.mkDOISource
  "Iris Marion Young"
  "Inclusion and Democracy"
  "Oxford University Press"
  "2000/2002"
  "10.1093/0198297556.001.0001"
  "https://doi.org/10.1093/0198297556.001.0001"
  Source.academicBookSource
  "Primary conceptual source distinguishing exclusion from deliberative access from exclusion operating within communication after access, including norms that disadvantage some forms of expression. It motivates an internal-exclusion / effective-communicative-influence coordinate distinct from mere presence or formal participation. It does not supply a universal ranking of democratic institutions or a DASHI consumer theorem."
  Source.publicAttribution

-- Reuse, not reacquisition. This exact source object is already owned by the
-- canonical Ibrahim Indigenous-memory/braiding lane.
bartlettTwoEyedCoLearningSource : Source.AttributedSource
bartlettTwoEyedCoLearningSource = IndigenousFollow.bartlettTwoEyedSource

acquisitionExtensionFourAtlas : Source.AttributedSourceAtlas
acquisitionExtensionFourAtlas = Source.mkSourceAtlas
  "Cohn institutional Ibrahim/QID/Dewey acquisition extension four"
  "DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFourExact"
  (medinaEpistemologyOfProtest ∷
   youngInclusionAndDemocracy ∷
   bartlettTwoEyedCoLearningSource ∷ [])
  "Two newly acquired conceptual donors plus one canonical in-repo Two-Eyed Seeing reuse. Medina contributes epistemic activism/resistant uptake; Young contributes internal exclusion/effective communicative influence; Bartlett-Marshall-Marshall is reused for co-learning without epistemic fusion. Source identity remains distinct from theorem ownership, institutional fact, motive and authority."

------------------------------------------------------------------------
-- QID / identity state.
--
-- Publication and author QIDs for Medina/Young are left unresolved in this
-- pass because no exact same-object Wikidata item was independently verified.
-- The existing Indigenous follow already retains verified concept QIDs for
-- traditional knowledge / traditional ecological knowledge while keeping the
-- general Two-Eyed Seeing concept QID unresolved. We consume that boundary
-- rather than manufacturing new IDs.
------------------------------------------------------------------------

medinaIdentifierState : String
medinaIdentifierState =
  "José Medina author QID unresolved; Epistemology of Protest publication QID unresolved; DOI is bibliographic identity only"

youngIdentifierState : String
youngIdentifierState =
  "Iris Marion Young author QID unresolved; Inclusion and Democracy publication QID unresolved; DOI is bibliographic identity only"

bartlettIdentifierReuseState : String
bartlettIdentifierReuseState =
  "reuse canonical Ibrahim owner: traditional knowledge Q1428168 and traditional ecological knowledge Q7832334 retained as concept identities; exact general Two-Eyed Seeing concept QID and Bartlett publication-item QID remain unresolved"

------------------------------------------------------------------------
-- Dewey coordinates are broad subject-space navigation only, not verified
-- publication-specific catalogue assignments.
------------------------------------------------------------------------

socialEpistemologyDewey : String
socialEpistemologyDewey = "121.000"

democraticParticipationDewey : String
democraticParticipationDewey = "320.000"

twoEyedDeweyState : String
twoEyedDeweyState =
  "unresolved publication-specific DDC; canonical Ibrahim Indigenous follow explicitly leaves traditional/Indigenous knowledge Dewey unresolved"

------------------------------------------------------------------------
-- Candidate coordinate families.
------------------------------------------------------------------------

medinaEpistemicActivismCoordinate : Ibrahim.DashiKnowledgeCoordinate
medinaEpistemicActivismCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary conceptual source coordinate"
  "epistemic activism / communicative resistance / proper uptake of protest"
  socialEpistemologyDewey
  "author and publication QIDs unresolved"
  "doi:10.1093/oso/9780197660904.001.0001"

youngInternalExclusionCoordinate : Ibrahim.DashiKnowledgeCoordinate
youngInternalExclusionCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary conceptual source coordinate"
  "internal exclusion / effective communicative influence after formal access"
  democraticParticipationDewey
  "author and publication QIDs unresolved"
  "doi:10.1093/0198297556.001.0001"

bartlettCoLearningCoordinate : Ibrahim.DashiKnowledgeCoordinate
bartlettCoLearningCoordinate = Ibrahim.dashi-knowledge-coordinate
  "canonical in-repo source reuse coordinate"
  "Two-Eyed Seeing co-learning / coordinated use without epistemic fusion"
  "Dewey unresolved in canonical Ibrahim Indigenous follow"
  "traditional knowledge Q1428168; traditional ecological knowledge Q7832334; Two-Eyed Seeing concept/publication QID unresolved"
  "doi:10.1007/s13412-012-0086-8"

------------------------------------------------------------------------
-- Ibrahim first-link follow into the already-owned least-coordinate frontier.
------------------------------------------------------------------------

medinaToEpistemicActivism : Ibrahim.DashiFirstLinkEdge
medinaToEpistemicActivism = Ibrahim.dashi-first-link-edge
  medinaEpistemicActivismCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "When a consumer fibre differs not merely by whether testimony was heard but by whether resistant collective communication can perturb settled ignorance, epistemic activism/proper uptake is a candidate coordinate. Protest does not itself create truth or proof authority."
  true

youngToInternalExclusion : Ibrahim.DashiFirstLinkEdge
youngToInternalExclusion = Ibrahim.dashi-first-link-edge
  youngInternalExclusionCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "A person or group can be formally present in deliberation while communicative norms still prevent effective influence. This candidate refines 'who is at the table' beyond absence and participation-power, but requires an actual consumer collision before admission to repair."
  true

bartlettToCoLearningReuse : Ibrahim.DashiFirstLinkEdge
bartlettToCoLearningReuse = Ibrahim.dashi-first-link-edge
  bartlettCoLearningCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The canonical Two-Eyed source is reused as a co-learning/process candidate: coordinated inquiry may draw on distinct knowledge systems without making them definitionally identical. Existing provenance, authority, permission and obligation boundaries remain authoritative."
  true

------------------------------------------------------------------------
-- Promotion / attribution firewall.
------------------------------------------------------------------------

record AcquisitionFourBoundary : Set where
  constructor acquisition-four-boundary
  field
    medinaEpistemicActivismAdded : Bool
    youngInternalExclusionAdded : Bool
    bartlettTwoEyedSourceReused : Bool

    formalPresenceDeterminesEffectiveCommunicativeInfluence : Bool
    protestCreatesProofAuthority : Bool
    twoEyedCoLearningImpliesEpistemicFusion : Bool
    unverifiedPublicationQidMayBeInvented : Bool
    authorQidMaySubstitutePublicationQid : Bool
    deweyAdjacencyCreatesSourceAuthority : Bool
    sourceAdjacencyAutomaticallySelectsResidual : Bool

open AcquisitionFourBoundary public

canonicalAcquisitionFourBoundary : AcquisitionFourBoundary
canonicalAcquisitionFourBoundary = acquisition-four-boundary
  true true true
  false false false false false false false

medinaCitationDoesNotImportProof :
  Source.citationImportsProof medinaEpistemologyOfProtest ≡ false
medinaCitationDoesNotImportProof = refl

youngCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority youngInclusionAndDemocracy ≡ false
youngCitationDoesNotCreateAuthority = refl

bartlettReuseDoesNotCreateAuthority :
  Source.citationCreatesAuthority bartlettTwoEyedCoLearningSource ≡ false
bartlettReuseDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Updated Pareto frontier.
------------------------------------------------------------------------

record AcquisitionFourFrontier : Set where
  constructor acquisition-four-frontier
  field
    priorAddedFamilies : String
    newlyAddedFamilies : String
    canonicalReuse : String
    qidDeweyDebt : String
    nextProofUse : String
    stopRule : String

open AcquisitionFourFrontier public

canonicalAcquisitionFourFrontier : AcquisitionFourFrontier
canonicalAcquisitionFourFrontier = acquisition-four-frontier
  "persistent structural epistemic exclusion; epistemic labour burden; outsider-within standpoint; participation power; Two-Eyed coexistence/co-production/action responsibility"
  "collective epistemic activism/resistant uptake; internal exclusion/effective communicative influence"
  "Bartlett-Marshall-Marshall 2012 co-learning source is reused from IbrahimSnowballMandelaReligionIndigenousMemoryBraidingBidiExact rather than reacquired"
  "Medina/Young author and publication QIDs unresolved; publication-specific Dewey assignments unresolved; canonical traditional-knowledge concept QIDs may not substitute for article/book identity"
  "test internal exclusion and epistemic activism beside the existing residual family only on a declared institutional fibre; retain Bartlett co-learning as a process coordinate where coexistence is present but joint inquiry/uptake differs"
  "continue the Ibrahim follow only when a branch pays a distinct consumer-relevant failure mode, a missing same-object identity, or an empirically required premise; stop branches that merely rename participation, uptake, refusal, standpoint, power or coexistence already represented"

priorAcquisitionBoundary : Prior.AcquisitionThreeBoundary
priorAcquisitionBoundary = Prior.canonicalAcquisitionThreeBoundary

canonicalTwoEyedSourceAnchor : Source.AttributedSource
canonicalTwoEyedSourceAnchor = IndigenousFollow.bartlettTwoEyedSource

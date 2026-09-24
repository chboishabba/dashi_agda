module DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.CohnInstitutionalIbrahimDeweyTraversalExact as Traversal
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionTwoExact as Prior
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

------------------------------------------------------------------------
-- THIRD IBRAHIM / DEWEY ACQUISITION EXTENSION
--
-- Pareto criterion: add a source only when it contributes a candidate failure
-- mode not already represented by testimony non-uptake, plural interpretive
-- resources, constructed ignorance, hermeneutical refusal, or generic critical
-- uptake.
--
-- Added families:
--   Dotson      : persistent / structural epistemic exclusion;
--   Berenstain  : coerced epistemic labour / epistemic exploitation;
--   Collins     : outsider-within situated standpoint;
--   Arnstein    : participation/presence versus actual decision power;
--   Reid et al. : Two-Eyed Seeing coexistence + action/co-production without
--                 assimilation into one knowledge system.
--
-- The sources motivate candidate coordinates only. They do not establish any
-- institutional fact, select a repair, prove bad faith, or import authority.
------------------------------------------------------------------------

dotsonConceptualizingEpistemicOppression : Source.AttributedSource
dotsonConceptualizingEpistemicOppression = Source.mkDOISource
  "Kristie Dotson"
  "Conceptualizing Epistemic Oppression"
  "Social Epistemology 28(2), 115-138"
  "2014"
  "10.1080/02691728.2013.782585"
  "https://doi.org/10.1080/02691728.2013.782585"
  Source.academicArticleSource
  "Primary conceptual source for persistent epistemic exclusion that hinders contribution to knowledge production, including exclusions whose repair difficulty lies in epistemic power or resilient epistemological systems. It motivates a structural-epistemic-exclusion coordinate distinct from one-off testimony non-uptake; it does not prove any particular institution is epistemically oppressive."
  Source.publicAttribution

berenstainEpistemicExploitation : Source.AttributedSource
berenstainEpistemicExploitation = Source.mkDOISource
  "Nora Berenstain"
  "Epistemic Exploitation"
  "Ergo 3(22), 569-590"
  "2016"
  "10.3998/ergo.12405314.0003.022"
  "https://doi.org/10.3998/ergo.12405314.0003.022"
  Source.academicArticleSource
  "Primary conceptual source for epistemic exploitation: marginalized people may be compelled to perform unrecognized, uncompensated, emotionally taxing epistemic labour educating privileged people about oppression. It motivates an epistemic-labour/burden coordinate distinct from silencing, absence and hermeneutical refusal; it does not establish coercion in a concrete DASHI fixture."
  Source.publicAttribution

collinsOutsiderWithin : Source.AttributedSource
collinsOutsiderWithin = Source.mkDOISource
  "Patricia Hill Collins"
  "Learning from the Outsider Within: The Sociological Significance of Black Feminist Thought"
  "Social Problems 33(6), S14-S32"
  "1986"
  "10.2307/800672"
  "https://doi.org/10.2307/800672"
  Source.academicArticleSource
  "Primary conceptual source for the outsider-within standpoint: marginal institutional location can support distinctive critical knowledge, self-definition and attention to interlocking oppression. It motivates a situated-standpoint coordinate; it does not imply that marginality automatically produces truth or that one standpoint universally dominates another."
  Source.publicAttribution

arnsteinCitizenParticipation : Source.AttributedSource
arnsteinCitizenParticipation = Source.mkDOISource
  "Sherry R. Arnstein"
  "A Ladder Of Citizen Participation"
  "Journal of the American Institute of Planners 35(4), 216-224"
  "1969"
  "10.1080/01944366908977225"
  "https://doi.org/10.1080/01944366908977225"
  Source.academicArticleSource
  "Primary participation-power source distinguishing mere information/consultation/placation from forms with greater citizen power over decisions. It motivates a participation-power coordinate for 'who is at the table' audits: visible inclusion or consultation does not by itself determine decision power. The historical ladder is not imported as a universal governance ranking."
  Source.publicAttribution

reidTwoEyedSeeingOperational : Source.AttributedSource
reidTwoEyedSeeingOperational = Source.mkDOISource
  "Andrea J. Reid; Lauren E. Eckert; John-Francis Lane; Nathan Young; Scott G. Hinch; Chris T. Darimont; Steven J. Cooke; Natalie C. Ban; Albert Marshall"
  "Two-Eyed Seeing: An Indigenous framework to transform fisheries research and management"
  "Fish and Fisheries 22(2), 243-261"
  "2021"
  "10.1111/faf.12516"
  "https://doi.org/10.1111/faf.12516"
  Source.academicArticleSource
  "Primary operational Two-Eyed Seeing source for knowledge coexistence and complementarity rather than assimilation: case studies co-develop questions, document and mobilize knowledge, and co-produce insights and decisions, with an explicit action/responsibility imperative. It motivates coexistence/action and co-production coordinates; it does not collapse Indigenous and Western knowledge histories or manufacture consumer adequacy."
  Source.publicAttribution

acquisitionExtensionThreeAtlas : Source.AttributedSourceAtlas
acquisitionExtensionThreeAtlas = Source.mkSourceAtlas
  "Cohn institutional Ibrahim/Dewey acquisition extension three"
  "DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact"
  (dotsonConceptualizingEpistemicOppression ∷
   berenstainEpistemicExploitation ∷
   collinsOutsiderWithin ∷
   arnsteinCitizenParticipation ∷
   reidTwoEyedSeeingOperational ∷ [])
  "Pareto source extension for structural epistemic exclusion, epistemic labour burden, outsider-within standpoint, participation power and operational Two-Eyed Seeing coexistence/action. Citation does not import proof, institutional fact, motive, authority or repair selection."

------------------------------------------------------------------------
-- Verified external identity coordinates where available.
-- Publication QIDs are intentionally left unresolved in this tranche.
------------------------------------------------------------------------

patriciaHillCollinsAuthorQid : Id.ItemId
patriciaHillCollinsAuthorQid = Id.itemId "Q465252"

sherryArnsteinAuthorQid : Id.ItemId
sherryArnsteinAuthorQid = Id.itemId "Q24170911"

identifierState : String
identifierState =
  "Collins author Q465252 and Arnstein author Q24170911 verified; Dotson, Berenstain and Reid author QIDs plus all five publication-item QIDs remain unresolved in this tranche. Author QIDs never substitute for publication QIDs."

------------------------------------------------------------------------
-- Broad Dewey coordinates are navigation only.
------------------------------------------------------------------------

socialEpistemologyDewey : String
socialEpistemologyDewey = "121.000"

socialGroupsParticipationDewey : String
socialGroupsParticipationDewey = "305.000"

publicAdministrationParticipationDewey : String
publicAdministrationParticipationDewey = "323.000"

indigenousKnowledgeNavigationDewey : String
indigenousKnowledgeNavigationDewey = "001.000"

------------------------------------------------------------------------
-- Candidate coordinate families.
------------------------------------------------------------------------

dotsonStructuralExclusionCoordinate : Ibrahim.DashiKnowledgeCoordinate
dotsonStructuralExclusionCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "persistent structural epistemic exclusion / epistemological-system resilience"
  socialEpistemologyDewey
  "publication and author QIDs unresolved"
  "doi:10.1080/02691728.2013.782585"

berenstainEpistemicLabourCoordinate : Ibrahim.DashiKnowledgeCoordinate
berenstainEpistemicLabourCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "epistemic exploitation / coerced explanatory labour burden"
  socialEpistemologyDewey
  "publication and author QIDs unresolved"
  "doi:10.3998/ergo.12405314.0003.022"

collinsOutsiderWithinCoordinate : Ibrahim.DashiKnowledgeCoordinate
collinsOutsiderWithinCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "outsider-within situated standpoint / marginal institutional location"
  socialGroupsParticipationDewey
  "publication QID unresolved; Patricia Hill Collins author Q465252 retained separately"
  "doi:10.2307/800672"

arnsteinParticipationPowerCoordinate : Ibrahim.DashiKnowledgeCoordinate
arnsteinParticipationPowerCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "participation presence / consultation / actual decision-power distinction"
  publicAdministrationParticipationDewey
  "publication QID unresolved; Sherry Arnstein author Q24170911 retained separately"
  "doi:10.1080/01944366908977225"

reidTwoEyedCoexistenceCoordinate : Ibrahim.DashiKnowledgeCoordinate
reidTwoEyedCoexistenceCoordinate = Ibrahim.dashi-knowledge-coordinate
  "external primary source coordinate"
  "Two-Eyed Seeing knowledge coexistence / co-production / action responsibility"
  indigenousKnowledgeNavigationDewey
  "publication and author QIDs unresolved"
  "doi:10.1111/faf.12516"

------------------------------------------------------------------------
-- Typed traversal into the existing least-coordinate repair frontier.
------------------------------------------------------------------------

dotsonToStructuralExclusion : Ibrahim.DashiFirstLinkEdge
dotsonToStructuralExclusion = Ibrahim.dashi-first-link-edge
  dotsonStructuralExclusionCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Persistent exclusion may live in epistemic power or resilient epistemological systems rather than in one failed testimony event. DASHI must still construct the consumer collision and test whether this coordinate separates it."
  true

berenstainToEpistemicLabour : Ibrahim.DashiFirstLinkEdge
berenstainToEpistemicLabour = Ibrahim.dashi-first-link-edge
  berenstainEpistemicLabourCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Being invited to explain or participate can itself impose asymmetric epistemic labour. This is distinct from being silenced or absent, and it remains a candidate coordinate until a declared consumer demonstrates separation."
  true

collinsToSituatedStandpoint : Ibrahim.DashiFirstLinkEdge
collinsToSituatedStandpoint = Ibrahim.dashi-first-link-edge
  collinsOutsiderWithinCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Institutional presence does not erase situated standpoint. Outsider-within location is a candidate coordinate for what a coarse institutional surface fails to retain; marginality itself is not promoted to truth authority."
  true

arnsteinToParticipationPower : Ibrahim.DashiFirstLinkEdge
arnsteinToParticipationPower = Ibrahim.dashi-first-link-edge
  arnsteinParticipationPowerCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "A 'who is at the table' audit must distinguish presence/consultation from actual decision influence or control. The historical ladder motivates the coordinate; DASHI does not import it as a universal ranking."
  true

reidToTwoEyedCoexistenceAction : Ibrahim.DashiFirstLinkEdge
reidToTwoEyedCoexistenceAction = Ibrahim.dashi-first-link-edge
  reidTwoEyedCoexistenceCoordinate
  Traversal.leastCoordinateRepairCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Two-Eyed Seeing contributes a candidate coexistence/action coordinate: multiple knowledge systems may remain distinct while jointly shaping questions, evidence and decisions. Coordination does not imply epistemic fusion or equal realised institutional power."
  true

------------------------------------------------------------------------
-- Attribution and promotion firewall.
------------------------------------------------------------------------

record AcquisitionThreeBoundary : Set where
  constructor acquisition-three-boundary
  field
    structuralEpistemicExclusionAdded : Bool
    epistemicLabourBurdenAdded : Bool
    outsiderWithinStandpointAdded : Bool
    participationPowerAdded : Bool
    twoEyedCoexistenceActionAdded : Bool

    presenceEqualsDecisionPower : Bool
    marginalStandpointAutomaticallyCreatesTruth : Bool
    epistemicLabourEqualsSilencing : Bool
    structuralExclusionEqualsSingleTestimonyFailure : Bool
    twoEyedCoexistenceEqualsEpistemicFusion : Bool

    sourceIdentityAutomaticallySelectsResidual : Bool
    acquisitionCreatesInstitutionalFact : Bool
    citationCreatesDashiAuthority : Bool
    authorQidMaySubstitutePublicationQid : Bool

open AcquisitionThreeBoundary public

canonicalAcquisitionThreeBoundary : AcquisitionThreeBoundary
canonicalAcquisitionThreeBoundary = acquisition-three-boundary
  true true true true true
  false false false false false
  false false false false

dotsonCitationDoesNotImportProof :
  Source.citationImportsProof dotsonConceptualizingEpistemicOppression ≡ false
dotsonCitationDoesNotImportProof = refl

berenstainCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority berenstainEpistemicExploitation ≡ false
berenstainCitationDoesNotCreateAuthority = refl

collinsCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority collinsOutsiderWithin ≡ false
collinsCitationDoesNotCreateAuthority = refl

arnsteinCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority arnsteinCitizenParticipation ≡ false
arnsteinCitationDoesNotCreateAuthority = refl

reidCitationDoesNotImportProof :
  Source.citationImportsProof reidTwoEyedSeeingOperational ≡ false
reidCitationDoesNotImportProof = refl

------------------------------------------------------------------------
-- Updated Pareto frontier.
------------------------------------------------------------------------

record AcquisitionThreeFrontier : Set where
  constructor acquisition-three-frontier
  field
    alreadyRepresentedFamilies : String
    addedFamilies : String
    deferredSnowballDonors : String
    nextProofUse : String
    stopRule : String

open AcquisitionThreeFrontier public

canonicalAcquisitionThreeFrontier : AcquisitionThreeFrontier
canonicalAcquisitionThreeFrontier = acquisition-three-frontier
  "evidential context/criticism; testimony uptake/silencing; plural interpretive resources; constructed ignorance; hermeneutical refusal; social/internal critical uptake"
  "persistent structural epistemic exclusion; epistemic labour burden; outsider-within situated standpoint; participation power; Two-Eyed Seeing coexistence/co-production/action responsibility"
  "Medina 2013 resistance/epistemic friction and Reid-McGregor et al. 2024 relational research ethics remain useful snowball donors, but overlap more strongly with already represented families than the five sources admitted here"
  "instantiate these five candidate families beside the existing six residual candidates only when a concrete institutional consumer exposes the corresponding debt; test actual fibre separation before admission to minimal repair or probe scheduling"
  "stop acquisition when a source merely renames an existing coordinate family; continue only for a distinct failure mode, an unresolved source/provenance identity, or an empirically required premise"

priorAcquisitionBoundary : Prior.AcquisitionTwoAttributionBoundary
priorAcquisitionBoundary = Prior.canonicalAcquisitionTwoAttributionBoundary

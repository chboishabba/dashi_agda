module DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom
import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact as Dependency
import DASHI.Law.SensibLawWoogarooKoalaScienceSnowballExact as Science

------------------------------------------------------------------------
-- WOOGAROO × IBRAHIM / DEWEY / DOI / QID / LEGAL ATOM CROSS-POLLINATION
--
-- This owner does not invent a second knowledge graph.  It applies the
-- canonical Ibrahim-style DASHI coordinate/edge surface to the existing
-- Woogaroo source Snowball and legal-atom consumers.
--
-- Coordinates remain deliberately distinct:
--   Dewey = repository/classification coordinate
--   DOI = publication identity
--   QID = external entity identity
--   source role = provenance/evidentiary role
--   legal atom = consumer-specific proposition required by the legal route
-- None of those coordinates is proof of another.
------------------------------------------------------------------------

data EvidenceRole : Set where
  primaryStatute : EvidenceRole
  primaryGovernmentStatus : EvidenceRole
  primaryProjectEvidence : EvidenceRole
  primaryApprovalRecord : EvidenceRole
  peerReviewedMechanism : EvidenceRole
  regionalComparatorScience : EvidenceRole
  methodologicalGuidance : EvidenceRole
  traversalMethodSource : EvidenceRole

data SameObjectStatus : Set where
  sameObject : SameObjectStatus
  sameRegionNotSameObject : SameObjectStatus
  generalMethodOnly : SameObjectStatus
  identityOpen : SameObjectStatus

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

habitatFragmentationQid : Id.ItemId
habitatFragmentationQid = Id.itemId "Q913302"

queenslandQid : Id.ItemId
queenslandQid = Id.itemId "Q36074"

lawDewey : String
lawDewey = "340.000"

biologyDewey : String
biologyDewey = "570.000"

------------------------------------------------------------------------
-- Attributed sources added by this cross-pollination.
------------------------------------------------------------------------

ibrahim2017 : Source.AttributedSource
ibrahim2017 = Source.mkDOISource
  "Mostafa Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Wikipedia First Link Network"
  "Journal of Computational Science 20, 118-126"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Source.academicArticleSource
  "Method source for deterministic first-link/traversal analysis only; it does not supply ecological or legal evidence for Woogaroo."
  Source.publicAttribution

taclaEtAl2025 : Source.AttributedSource
taclaEtAl2025 = Source.mkDOISource
  "Philippa Kirsten Tacla; Benjamin James Barth; Sean Ian FitzGibbon; Amber Kristen Gillett; William Anthony Ellis"
  "Patterns of activity and travel by koalas in a disturbed urban landscape in Queensland"
  "Australian Mammalogy 47, AM24044"
  "2025"
  "10.1071/AM24044"
  "https://doi.org/10.1071/AM24044"
  Source.academicArticleSource
  "University of Queensland movement study using GPS collars in a changing Queensland landscape; supports mechanism/method questions about movement through fragmented urban habitat, not a Springview same-object conclusion."
  Source.publicAttribution

ibrahimWoogarooSourceAtlas : Source.AttributedSourceAtlas
ibrahimWoogarooSourceAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim/Dewey/QID/DOI legal-atom source atlas"
  "DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact"
  (ibrahim2017 ∷
   taclaEtAl2025 ∷
   Science.source Science.endangeredKoalaHabitatGuidance ∷
   Science.source Science.bruntonConnectivityReview ∷
   Science.source Science.mclennanGenomicsStudy ∷
   Science.source Science.dexterSEQVehicleStrikeStudy ∷
   Science.source Science.mcleanMovementStudy ∷ [])
  "Traversal method plus current official/peer-reviewed koala science. DOI/QID/Dewey coordinates preserve identity and navigation only. General or regional science does not become same-object Springview evidence without a separate join."

------------------------------------------------------------------------
-- Knowledge coordinates.  Broad Dewey parents are reused rather than
-- inventing highly specific decimal classes that are not owned by the repo.
------------------------------------------------------------------------

s102StatutoryCoordinate : Ibrahim.DashiKnowledgeCoordinate
s102StatutoryCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact.agda"
  "Queensland NCA ss 12, 102-103 statutory consumer"
  lawDewey
  (Id.rawItemId queenslandQid)
  "Queensland Nature Conservation Act 1992 current text"

koalaEntityCoordinate : Ibrahim.DashiKnowledgeCoordinate
koalaEntityCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact.agda"
  "Koala threatened-wildlife identity/status proposition"
  biologyDewey
  (Id.rawItemId koalaQid)
  "Queensland Government threatened-species status source"

fragmentationCoordinate : Ibrahim.DashiKnowledgeCoordinate
fragmentationCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooKoalaScienceSnowballExact.agda"
  "habitat fragmentation / functional connectivity mechanism"
  biologyDewey
  (Id.rawItemId habitatFragmentationQid)
  "doi:10.1002/2688-8319.70253"

uqUrbanMovementCoordinate : Ibrahim.DashiKnowledgeCoordinate
uqUrbanMovementCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimDeweyQidLegalAtomExact.agda"
  "UQ urban koala movement mechanism source"
  biologyDewey
  (Id.rawItemId koalaQid)
  "doi:10.1071/AM24044"

genomicsCoordinate : Ibrahim.DashiKnowledgeCoordinate
genomicsCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooKoalaScienceSnowballExact.agda"
  "range-wide koala genomics / population-structure source"
  biologyDewey
  (Id.rawItemId koalaQid)
  "doi:10.1002/eap.3062"

projectEcologyCoordinate : Ibrahim.DashiKnowledgeCoordinate
projectEcologyCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooEvidenceDependencyMatrixExact.agda"
  "Springview/Woogaroo same-project SHG ecology"
  biologyDewey
  (Id.rawItemId koalaQid)
  "SHG 2019 project ecology / existing attributed project carrier"

s13EssentialityCoordinate : Ibrahim.DashiKnowledgeCoordinate
s13EssentialityCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooS13EssentialityStressTestExact.agda"
  "Queensland NCA s 13 viable-population essentiality consumer"
  lawDewey
  (Id.rawItemId queenslandQid)
  "Queensland Nature Conservation Act 1992 s 13 current text"

------------------------------------------------------------------------
-- Typed Ibrahim-style edges.  'supportedBy' never means same-object payment;
-- 'dependsOn' is reserved for a genuine consumer prerequisite.
------------------------------------------------------------------------

fragmentationSupportsS102 : Ibrahim.DashiFirstLinkEdge
fragmentationSupportsS102 = Ibrahim.dashi-first-link-edge
  fragmentationCoordinate
  s102StatutoryCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Connectivity/fragmentation science supplies mechanism and expert-question structure; the s 102 legal conclusion still requires same-project/current evidence and Ministerial opinion."
  true

uqMovementSupportsS102 : Ibrahim.DashiFirstLinkEdge
uqMovementSupportsS102 = Ibrahim.dashi-first-link-edge
  uqUrbanMovementCoordinate
  s102StatutoryCoordinate
  Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Current Queensland movement evidence supports the biological plausibility that fragmented urban landscapes alter movement/use; it is not Springview-specific exposure or effect evidence."
  true

genomicsSupportsS13Method : Ibrahim.DashiFirstLinkEdge
genomicsSupportsS13Method = Ibrahim.dashi-first-link-edge
  genomicsCoordinate
  s13EssentialityCoordinate
  Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Population-genomic structure and gene-flow evidence help define what a viable population/connectivity inquiry should measure; the paper does not identify the Springview population."
  true

projectEcologyDependsIntoS102 : Ibrahim.DashiFirstLinkEdge
projectEcologyDependsIntoS102 = Ibrahim.dashi-first-link-edge
  projectEcologyCoordinate
  s102StatutoryCoordinate
  Ibrahim.dependsOn
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The live Woogaroo s 102 case depends on same-project ecological exposure/effect evidence rather than literature mechanism alone."
  true

projectEcologyDependsIntoS13 : Ibrahim.DashiFirstLinkEdge
projectEcologyDependsIntoS13 = Ibrahim.dashi-first-link-edge
  projectEcologyCoordinate
  s13EssentialityCoordinate
  Ibrahim.dependsOn
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The s 13 case requires same-project habitat-function evidence, but that evidence does not itself pay viable-population identity or essentiality."
  true

------------------------------------------------------------------------
-- Legal atom intersection.
------------------------------------------------------------------------

record KnowledgeAtomBinding : Set where
  constructor knowledge-atom-binding
  field
    coordinate : Ibrahim.DashiKnowledgeCoordinate
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    role : EvidenceRole
    sameObjectStatus : SameObjectStatus
    admissibleAsInput : Bool
    sufficientForAtom : Bool
    note : String

open KnowledgeAtomBinding public

projectEcologyToS102Effect : KnowledgeAtomBinding
projectEcologyToS102Effect = knowledge-atom-binding
  projectEcologyCoordinate
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  primaryProjectEvidence
  sameObject
  true
  false
  "Strong same-project support for seriousness/exposure, but the Queensland likely-significant-detrimental-effect conclusion remains open."

fragmentationScienceToS102Effect : KnowledgeAtomBinding
fragmentationScienceToS102Effect = knowledge-atom-binding
  fragmentationCoordinate
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  peerReviewedMechanism
  generalMethodOnly
  true
  false
  "Mechanism evidence can inform an expert opinion but cannot replace current same-object effect evidence."

uqMovementToAffectedHabitat : KnowledgeAtomBinding
uqMovementToAffectedHabitat = knowledge-atom-binding
  uqUrbanMovementCoordinate
  Atom.affectedWildlifeHabitatAtom
  Atom.nca102InterimOrderConsumer
  peerReviewedMechanism
  sameRegionNotSameObject
  true
  false
  "Queensland urban movement evidence is regionally relevant context, not proof that the exact Springview habitat is currently used in the same way."

genomicsToS13Essentiality : KnowledgeAtomBinding
genomicsToS13Essentiality = knowledge-atom-binding
  genomicsCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  regionalComparatorScience
  sameRegionNotSameObject
  true
  false
  "Genomics informs population/connectivity questions but does not identify the local viable population or pay statutory essentiality."

projectEcologyToS13Essentiality : KnowledgeAtomBinding
projectEcologyToS13Essentiality = knowledge-atom-binding
  projectEcologyCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryProjectEvidence
  sameObject
  true
  false
  "Same-object habitat function is paid strongly; viable-population identity and the without-site essentiality counterfactual remain open."

------------------------------------------------------------------------
-- Coverage / Snowball frontier.
------------------------------------------------------------------------

record WoogarooIbrahimCoverage : Set where
  constructor woogaroo-ibrahim-coverage
  field
    deweyCoordinatesPresent : Bool
    doiIdentitiesPresent : Bool
    qidIdentitiesPresent : Bool
    primarySourceRolesSeparated : Bool
    peerReviewedContextSeparated : Bool
    legalAtomsBound : Bool
    sameObjectStatusExplicit : Bool
    qidOrDoiPromotesLegalAtom : Bool
    firstUnpaidS102 : String
    firstUnpaidS13 : String

currentWoogarooIbrahimCoverage : WoogarooIbrahimCoverage
currentWoogarooIbrahimCoverage = woogaroo-ibrahim-coverage
  true true true true true true true false
  "Independent current ecological opinion applying the exact s 12/s 102 wording to the approved/current project state, with mitigation and current execution facts addressed."
  "Independent identification of the relevant viable Koala population/community, followed by the without-Springview-habitat persistence/connectivity counterfactual."

------------------------------------------------------------------------
-- Explicit attribution / WrongType boundaries.
------------------------------------------------------------------------

data DoiEqualsScientificTruth : Set where
data QidEqualsLegalAtom : Set where
data DeweyClassEqualsSemanticDependence : Set where
data RegionalPaperEqualsSameObjectEvidence : Set where
data PrimarySourceEqualsLegalConclusion : Set where
data ManyCitationsEqualIndependentCarriers : Set where
data SupportedByEqualsDependsOn : Set where

doiDoesNotCreateScientificTruth : DoiEqualsScientificTruth → ⊥
doiDoesNotCreateScientificTruth ()

qidDoesNotCreateLegalAtom : QidEqualsLegalAtom → ⊥
qidDoesNotCreateLegalAtom ()

deweyDoesNotCreateSemanticDependence : DeweyClassEqualsSemanticDependence → ⊥
deweyDoesNotCreateSemanticDependence ()

regionalPaperDoesNotBecomeSameObjectEvidence : RegionalPaperEqualsSameObjectEvidence → ⊥
regionalPaperDoesNotBecomeSameObjectEvidence ()

primarySourceDoesNotCreateLegalConclusion : PrimarySourceEqualsLegalConclusion → ⊥
primarySourceDoesNotCreateLegalConclusion ()

citationMultiplicityDoesNotCreateIndependentCarriers : ManyCitationsEqualIndependentCarriers → ⊥
citationMultiplicityDoesNotCreateIndependentCarriers ()

supportDoesNotBecomeDependency : SupportedByEqualsDependsOn → ⊥
supportDoesNotBecomeDependency ()

------------------------------------------------------------------------
-- Reuse the existing dependency accounting rather than recounting sources.
------------------------------------------------------------------------

s102DependencyState : Dependency.ConsumerDependencyState
s102DependencyState = Dependency.s102DependencyState

s13DependencyState : Dependency.ConsumerDependencyState
s13DependencyState = Dependency.s13DependencyState

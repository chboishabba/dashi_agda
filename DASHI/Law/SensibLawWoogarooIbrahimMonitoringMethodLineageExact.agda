module DASHI.Law.SensibLawWoogarooIbrahimMonitoringMethodLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact as Monitoring
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- THIN MONITORING-METHOD LINEAGE EXTENSION
--
-- Adds peer-reviewed provenance for SAT/Rapid-SAT style evidence and the
-- scale-confounding boundary for Koala habitat maps.  It extends the existing
-- Ibrahim/Dewey/QID/legal-atom owner; it does not create a second graph.
------------------------------------------------------------------------

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

koalaDewey : String
koalaDewey = "599.25"

conservationDewey : String
conservationDewey = "333.95"

methodsDewey : String
methodsDewey = "590.72"

satMethodSource : Source.AttributedSource
satMethodSource = Source.mkDOISource
  "Stephen Phillips; John Callaghan"
  "The Spot Assessment Technique: a tool for determining localised levels of habitat use by Koalas Phascolarctos cinereus"
  "Australian Zoologist 35(3)"
  "2011"
  "10.7882/AZ.2011.029"
  "https://doi.org/10.7882/AZ.2011.029"
  Source.academicArticleSource
  "Peer-reviewed method lineage for SAT-based Koala habitat-use evidence. It supports interpretation of Biolink/First Nine monitoring methods but does not validate the execution, sampling frame, representativeness or legal relevance of any particular local survey."
  Source.publicAttribution

mappingScaleSource : Source.AttributedSource
mappingScaleSource = Source.mkDOISource
  "Daniel L. Mitchell; Mariela Soto-Berelov; William T. Langford; Simon D. Jones"
  "Factors confounding koala habitat mapping at multiple decision-making scales"
  "Ecological Management & Restoration 22"
  "2021"
  "10.1111/emr.12468"
  "https://doi.org/10.1111/emr.12468"
  Source.academicArticleSource
  "Peer-reviewed calibration source on scale/method dependence in Koala habitat mapping. It supports the boundary between regional habitat maps, local field observations and parcel-specific legal consumers."
  Source.publicAttribution

monitoringMethodAtlas : Source.AttributedSourceAtlas
monitoringMethodAtlas = Source.mkSourceAtlas
  "Woogaroo Koala monitoring-method lineage"
  "DASHI.Law.SensibLawWoogarooIbrahimMonitoringMethodLineageExact"
  (satMethodSource ∷ mappingScaleSource ∷ [])
  "DOI-paid peer-reviewed method/calibration sources. They are method lineage only: DOI identity, peer review and general methodological validity do not pay local observations, viable-population identity, s 13 essentiality or s 102 likely significant detrimental effect."

satCoordinate : Ibrahim.DashiKnowledgeCoordinate
satCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimMonitoringMethodLineageExact.agda"
  "SAT / Rapid-SAT Koala habitat-use method lineage"
  methodsDewey
  (Id.rawItemId koalaQid)
  "doi:10.7882/AZ.2011.029"

mappingScaleCoordinate : Ibrahim.DashiKnowledgeCoordinate
mappingScaleCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimMonitoringMethodLineageExact.agda"
  "Koala habitat mapping scale/confounding calibration"
  conservationDewey
  (Id.rawItemId koalaQid)
  "doi:10.1111/emr.12468"

satSupportsMonitoringInterpretation : Ibrahim.DashiFirstLinkEdge
satSupportsMonitoringInterpretation = Ibrahim.dashi-first-link-edge
  satCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "SAT is a source-paid general method used in the local monitoring lineage. The local consumer still reopens survey execution, spatial sampling, temporal coverage and population inference."
  true

mappingScaleSupportsS13 : Ibrahim.DashiFirstLinkEdge
mappingScaleSupportsS13 = Ibrahim.dashi-first-link-edge
  mappingScaleCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Habitat maps at different scales answer different questions; a regional habitat layer cannot by itself identify the viable population or make a parcel essential under s 13."
  true

mappingScaleSupportsS102 : Ibrahim.DashiFirstLinkEdge
mappingScaleSupportsS102 = Ibrahim.dashi-first-link-edge
  mappingScaleCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Spatial mapping is evidence for exposure and causal pathways, but mapped habitat alone does not pay the s 102 likely-significant-detrimental-effect conclusion."
  true

record MethodAtomBinding : Set where
  constructor method-atom-binding
  field
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    admissibleAsMethodSupport : Bool
    localExecutionPaid : Bool
    consumerComplete : Bool
    contribution : String
    residual : String

open MethodAtomBinding public

satToS13 : MethodAtomBinding
satToS13 = method-atom-binding
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false false
  "Pays the method provenance for SAT-derived habitat-use observations in the Ipswich/Biolink/adjacent-project monitoring lineage."
  "Acquire the underlying local 2020/2023/2025 monitoring outputs and preserve their exact survey design/site/time receipts before using them to identify a viable population."

mappingToS102 : MethodAtomBinding
mappingToS102 = method-atom-binding
  Atom.affectedWildlifeHabitatAtom
  Atom.nca102InterimOrderConsumer
  true false false
  "Pays a scientific reason to keep regional maps, project habitat scores and local observations as different evidence scales."
  "Join current local monitoring/occurrence evidence to the approved process; do not treat mapping class as realised use or effect."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data PeerReviewedMethodEqualsLocalSurveyValid : Set where
data SATDetectionEqualsPopulationSize : Set where
data HabitatMapEqualsRealisedUse : Set where
data DoiEqualsLegalAtomPayment : Set where

methodDoesNotValidateLocalExecution : PeerReviewedMethodEqualsLocalSurveyValid → ⊥
methodDoesNotValidateLocalExecution ()

satDoesNotCreatePopulationSize : SATDetectionEqualsPopulationSize → ⊥
satDoesNotCreatePopulationSize ()

mapDoesNotCreateRealisedUse : HabitatMapEqualsRealisedUse → ⊥
mapDoesNotCreateRealisedUse ()

doiDoesNotPayLegalAtom : DoiEqualsLegalAtomPayment → ⊥
doiDoesNotPayLegalAtom ()

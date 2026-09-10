module DASHI.Law.SensibLawWoogarooS102StatutorySpatialRelationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- NCA ss 12, 102-103 SPATIAL-RELATION CORRECTION
--
-- This owner records the current statutory structure at source level.  It is
-- not legal advice.  It corrects an over-strong earlier engineering shorthand
-- in which an exact/perfect spatial overlap was treated as if it were itself
-- the statutory threshold for an interim conservation order.
------------------------------------------------------------------------

data S102QualifyingObject : Set where
  threatenedOrNearThreatenedWildlife : S102QualifyingObject
  ministerOpinionCriticalHabitat : S102QualifyingObject
  areaOfMajorInterest : S102QualifyingObject
  protectedArea : S102QualifyingObject

record S102StatutoryPredicate : Set where
  constructor s102-statutory-predicate
  field
    qualifyingObject : S102QualifyingObject
    subjectToThreateningProcess : Bool
    threateningProcessLikelySignificantDetrimentalEffect : Bool
    ministerOpinionRequired : Bool
    exactGeometryTextuallyRequired : Bool
    sameLandOccupationTextuallyRequired : Bool

open S102StatutoryPredicate public

s102TextualStructure : S102StatutoryPredicate
s102TextualStructure = s102-statutory-predicate
  threatenedOrNearThreatenedWildlife
  false
  false
  true
  false
  false

record ThreateningProcessDefinition : Set where
  constructor threatening-process-definition
  field
    mayThreatenSurvival : Bool
    mayAffectCapacityToSustainNaturalProcesses : Bool
    geometryIsEvidenceNotDefinition : Bool

currentThreateningProcessDefinition : ThreateningProcessDefinition
currentThreateningProcessDefinition = threatening-process-definition
  true true true

record OffSiteOrderCapacity : Set where
  constructor off-site-order-capacity
  field
    orderMayRelateToLandWithoutWildlifeWithinLand : Bool
    orderMayRelateToLandWithoutHabitatWithinLand : Bool
    exactOverlapNotNecessaryCondition : Bool

s103OffSiteOrderCapacity : OffSiteOrderCapacity
s103OffSiteOrderCapacity = off-site-order-capacity true true true

record S102RouteIndependence : Set where
  constructor s102-route-independence
  field
    wildlifeRouteExists : Bool
    criticalHabitatRouteExists : Bool
    priorS13ClassificationRequiredForEveryS102Case : Bool

s102RouteIndependence : S102RouteIndependence
s102RouteIndependence = s102-route-independence true true false

------------------------------------------------------------------------
-- Corrected role for spatial evidence.
------------------------------------------------------------------------

data SpatialEvidenceRole : Set where
  threateningProcessIdentification : SpatialEvidenceRole
  causalConnectionEvidence : SpatialEvidenceRole
  likelyEffectEvidence : SpatialEvidenceRole
  orderLandTargetingEvidence : SpatialEvidenceRole
  habitatFunctionEvidence : SpatialEvidenceRole

record SpatialConsumerBoundary : Set where
  constructor spatial-consumer-boundary
  field
    exactOverlapUseful : Bool
    exactOverlapLegallyMandatory : Bool
    nonOverlappingLandCanStillBeOrderLand : Bool
    processEffectRelationStillMustBeSupported : Bool
    description : String

currentSpatialConsumerBoundary : SpatialConsumerBoundary
currentSpatialConsumerBoundary = spatial-consumer-boundary
  true
  false
  true
  true
  "A12705838 georeferencing and habitat/species joins remain high-value evidence because they can identify the threatening process, affected ecological object, causal pathway and land to which an order could relate. But the current NCA text does not impose a perfect-overlap requirement, and s 103(2) expressly permits an order relating to land even where the wildlife or habitat is not within that land."

------------------------------------------------------------------------
-- Woogaroo-specific revised s 102 evidence target.
------------------------------------------------------------------------

record WoogarooS102EvidenceTarget : Set where
  constructor woogaroo-s102-evidence-target
  field
    approvedThreateningProcessObject : Bool
    negotiatedPlanScaleGeometry : Bool
    threatenedWildlifeOrQualifyingHabitatEvidence : Bool
    likelySignificantDetrimentalEffectEvidence : Bool
    exactPerfectOverlapRequired : Bool
    currentExecutionTimingStillUseful : Bool
    condition6aComplianceStillUseful : Bool
    nextLegalQuestion : String

currentWoogarooS102EvidenceTarget : WoogarooS102EvidenceTarget
currentWoogarooS102EvidenceTarget = woogaroo-s102-evidence-target
  true
  true
  true
  false
  false
  true
  true
  "Can the approved vegetation-clearing/earthworks process, viewed with the same-project Koala habitat/connectivity evidence and any current threatened-wildlife evidence, support the Ministerial opinion that a qualifying object is subject to a threatening process likely to have significant detrimental effect? Exact plan-to-habitat overlap strengthens that case but is not itself the statutory test."

------------------------------------------------------------------------
-- WrongType corrections.
------------------------------------------------------------------------

data PerfectOverlapEqualsS102StatutoryElement : Set where
data NoPerfectOverlapEqualsS102Unavailable : Set where
data PriorS13EqualsMandatoryS102Prerequisite : Set where
data ThreateningProcessEqualsPhysicalTreeIntersection : Set where
data S103OffSiteCapacityEqualsNoCausalConnectionNeeded : Set where

perfectOverlapIsNotStatutoryElement : PerfectOverlapEqualsS102StatutoryElement → ⊥
perfectOverlapIsNotStatutoryElement ()

lackOfPerfectOverlapDoesNotForecloseS102 : NoPerfectOverlapEqualsS102Unavailable → ⊥
lackOfPerfectOverlapDoesNotForecloseS102 ()

priorS13IsNotUniversalPrerequisite : PriorS13EqualsMandatoryS102Prerequisite → ⊥
priorS13IsNotUniversalPrerequisite ()

threateningProcessDoesNotCollapseToTreeIntersection : ThreateningProcessEqualsPhysicalTreeIntersection → ⊥
threateningProcessDoesNotCollapseToTreeIntersection ()

offSiteCapacityDoesNotEraseEffectRelation : S103OffSiteCapacityEqualsNoCausalConnectionNeeded → ⊥
offSiteCapacityDoesNotEraseEffectRelation ()

------------------------------------------------------------------------
-- Source-attribution note for a future statute-lineage owner.
------------------------------------------------------------------------

record CurrentStatutorySourceReceipt : Set where
  constructor current-statutory-source-receipt
  field
    source : String
    provisions : String
    sourceRole : String
    interpretationBoundary : String

currentNCAStatutorySourceReceipt : CurrentStatutorySourceReceipt
currentNCAStatutorySourceReceipt = current-statutory-source-receipt
  "Queensland Legislation — Nature Conservation Act 1992, current in-force text"
  "ss 12, 13, 102, 103, 105, 107"
  "primary legislation; s 12 defines threatening process, s 102 states the Ministerial interim-order predicate, s 103 defines possible order effects/spatial reach, s 105 duration and s 107 authority suspension"
  "Textual statutory reconstruction does not determine how the Minister, tribunal or court would apply the provisions to Woogaroo facts; counsel should validate procedure, discretion, reviewability and any regulations/conservation plans bearing on the route."

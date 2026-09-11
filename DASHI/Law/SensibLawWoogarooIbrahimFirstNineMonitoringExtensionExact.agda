module DASHI.Law.SensibLawWoogarooIbrahimFirstNineMonitoringExtensionExact where

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
-- THIN FIRST NINE / BROOKWATER MONITORING EXTENSION
--
-- Adjacent Greater Springfield monitoring is closer to the live Woogaroo
-- consumers than another generic fragmentation paper.  It remains a different
-- EPBC action and does not become Springview/Woogaroo same-object evidence.
------------------------------------------------------------------------

data SourceRelation : Set where
  adjacentGreaterSpringfieldProject : SourceRelation
  sameConsultancyDifferentProject : SourceRelation
  independentGovernmentComplianceCarrier : SourceRelation

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

springfieldQid : Id.ItemId
springfieldQid = Id.itemId "Q1838932"

ecologicalConnectivityQid : Id.ItemId
ecologicalConnectivityQid = Id.itemId "Q2993449"

koalaDewey : String
koalaDewey = "599.25"

ecologyDewey : String
ecologyDewey = "577"

conservationDewey : String
conservationDewey = "333.95"

------------------------------------------------------------------------
-- Attribution.
------------------------------------------------------------------------

firstNineACR2021 : Source.AttributedSource
firstNineACR2021 = Source.mkNoDOISource
  "Saunders Havill Group, for Springfield Land Corporation Pty Limited"
  "Annual Compliance Report — First Nine Master Planned Residential Development, EPBC 2016/7676, Year 3"
  "EPBC annual compliance report"
  "2021"
  "https://greaterspringfield.com.au/wp-content/uploads/2025/08/7399-EPBC-ACR-3.pdf"
  (Source.namedSourceKind "project compliance monitoring report")
  "Adjacent Brookwater/Greater Springfield project monitoring carrier. It reports a permitted 46.2 ha Koala-habitat impact and repeat SAT/scat monitoring in the offset area; 2020 monitoring recorded Koala usage across all offset-area land parcels and a high-use location adjacent to a rehabilitated area on the banks of Woogaroo Creek. Used as local monitoring/connectivity/restoration evidence, not as Springview occupancy or population identity."
  Source.publicAttribution

firstNineACR2024 : Source.AttributedSource
firstNineACR2024 = Source.mkNoDOISource
  "Saunders Havill Group, for Springfield Land Corporation Pty Limited"
  "Annual Compliance Report — First Nine Master Planned Residential Development, EPBC 2016/7676, Year 6"
  "EPBC annual compliance report"
  "2024"
  "https://greaterspringfield.com.au/wp-content/uploads/2024/06/7399-First-Nine-EPBC-ACR-6-062024.pdf"
  (Source.namedSourceKind "project compliance monitoring report")
  "Later compliance-report carrier confirming the Brookwater project identity, 47.25 ha project area, permitted impact to 46.2 ha of MNES Koala habitat, and ongoing approval/offset-monitoring lineage. Used to preserve longitudinal project identity, not to infer current Woogaroo effects."
  Source.publicAttribution

firstNineFederalAudit2025 : Source.AttributedSource
firstNineFederalAudit2025 = Source.mkNoDOISource
  "National Environmental Protection Agency / Department of Climate Change, Energy, the Environment and Water"
  "EPBC Act approvals audit program — EPBC 2016/7676 First Nine Master Planned Residential Development"
  "Commonwealth compliance audit summary"
  "2025"
  "https://www.nationalepa.gov.au/epbc/compliance/audits"
  Source.governmentSource
  "Independent government compliance carrier reporting 7 conditions compliant and 2 conditions non-compliant for EPBC 2016/7676 in the 2025 audit summary. The summary does not identify the two conditions in the currently acquired carrier and is used only to route acquisition of the full audit findings; it is not evidence of non-compliance by EPBC 2019/8575 or 9281/2024/OW."
  Source.publicAttribution

firstNineAtlas : Source.AttributedSourceAtlas
firstNineAtlas = Source.mkSourceAtlas
  "Woogaroo First Nine/Brookwater local monitoring Snowball"
  "DASHI.Law.SensibLawWoogarooIbrahimFirstNineMonitoringExtensionExact"
  (firstNineACR2021 ∷ firstNineACR2024 ∷ firstNineFederalAudit2025 ∷ [])
  "Adjacent-project ecological monitoring plus independent government compliance audit summary. The two SHG reports are a shared producer/project lineage, not two independent biological replications. The government audit is institutionally independent for compliance, not an independent replication of the Koala observations. DOI is not applicable; QID/Dewey are navigation coordinates only."

------------------------------------------------------------------------
-- Local monitoring receipt.
------------------------------------------------------------------------

record FirstNineKoalaMonitoringReceipt : Set where
  constructor first-nine-koala-monitoring-receipt
  field
    epbcReference : String
    projectLocation : String
    permittedKoalaHabitatImpactHa : String
    repeatSatMonitoringLocated : Bool
    usageAcrossOffsetLandParcelsReported : Bool
    highUsageAdjacentWoogarooCreekRehabilitationReported : Bool
    springviewSameObject : Bool
    independentFromSHGInstitution : Bool

open FirstNineKoalaMonitoringReceipt public

currentFirstNineReceipt : FirstNineKoalaMonitoringReceipt
currentFirstNineReceipt = first-nine-koala-monitoring-receipt
  "EPBC 2016/7676"
  "Brookwater, approximately 1 km north of Springfield Central"
  "46.2"
  true true true
  false false

------------------------------------------------------------------------
-- Ibrahim coordinates and legal-atom joins.
------------------------------------------------------------------------

firstNineMonitoringCoordinate : Ibrahim.DashiKnowledgeCoordinate
firstNineMonitoringCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimFirstNineMonitoringExtensionExact.agda"
  "First Nine/Brookwater longitudinal Koala SAT monitoring near Woogaroo Creek"
  koalaDewey
  (Id.rawItemId koalaQid)
  "primary: EPBC 2016/7676 Annual Compliance Report Year 3"

firstNineAuditCoordinate : Ibrahim.DashiKnowledgeCoordinate
firstNineAuditCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimFirstNineMonitoringExtensionExact.agda"
  "First Nine/Brookwater federal compliance audit"
  conservationDewey
  (Id.rawItemId springfieldQid)
  "primary: National EPA EPBC compliance audit summary, 2025"

firstNineToS13 : Ibrahim.DashiFirstLinkEdge
firstNineToS13 = Ibrahim.dashi-first-link-edge
  firstNineMonitoringCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Adjacent Brookwater monitoring records repeated Koala usage and a high-use location beside rehabilitated Woogaroo Creek. This makes local movement/population/restoration questions more concrete, but a different EPBC action cannot identify Springview's viable population or establish essentiality."
  true

firstNineToS102 : Ibrahim.DashiFirstLinkEdge
firstNineToS102 = Ibrahim.dashi-first-link-edge
  firstNineMonitoringCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Nearby repeated Koala-use monitoring supports local biological plausibility and the value of current local records. It is not a current-effect estimate for the 9281 clearing process."
  true

------------------------------------------------------------------------
-- Legal atom bindings.
------------------------------------------------------------------------

record FirstNineAtomBinding : Set where
  constructor first-nine-atom-binding
  field
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    relation : SourceRelation
    admissibleAsContext : Bool
    sameObjectPaid : Bool
    consumerComplete : Bool
    contribution : String
    residual : String

open FirstNineAtomBinding public

firstNineAffectedHabitatBinding : FirstNineAtomBinding
firstNineAffectedHabitatBinding = first-nine-atom-binding
  Atom.affectedWildlifeHabitatAtom
  Atom.nca102InterimOrderConsumer
  adjacentGreaterSpringfieldProject
  true false false
  "Adds repeat adjacent Koala-use observations associated with the Woogaroo Creek landscape rather than another generic mechanism paper."
  "Join current WildNet/Ipswich monitoring records to Opossum/Woogaroo/Springview and obtain an independent expert view of likely effect from the exact 9281 process."

firstNineEssentialityBinding : FirstNineAtomBinding
firstNineEssentialityBinding = first-nine-atom-binding
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  adjacentGreaterSpringfieldProject
  true false false
  "Shows nearby Woogaroo Creek habitat/restoration has been repeatedly used by Koalas within another Greater Springfield EPBC monitoring program."
  "Different action/offset area; identify realised connection and viable-population membership before using it for s 13 essentiality."

firstNineOffsetMaturityBinding : FirstNineAtomBinding
firstNineOffsetMaturityBinding = first-nine-atom-binding
  Atom.offsetVegetationMaturityAtom
  Atom.epbc8575OffsetAdequacyConsumer
  sameConsultancyDifferentProject
  true false false
  "Provides a local example where rehabilitation and Koala-use monitoring coexist, useful for asking how long restoration takes to provide demonstrated function."
  "Do not transfer performance, condition or maturation rate from First Nine to the final 2019/8575 offset parcels; acquire their exact baseline and monitoring data."

------------------------------------------------------------------------
-- Compliance Snowball is separate from ecological proof.
------------------------------------------------------------------------

record FirstNineAuditFrontier : Set where
  constructor first-nine-audit-frontier
  field
    governmentAuditSummaryPaid : Bool
    twoNonCompliancesReported : Bool
    exactNonCompliantConditionsPaid : Bool
    relevanceTo2019_8575CompliancePaid : Bool
    nextCut : String

currentFirstNineAuditFrontier : FirstNineAuditFrontier
currentFirstNineAuditFrontier = first-nine-audit-frontier
  true true false false
  "Acquire the full 2025 EPBC 2016/7676 audit finding or condition-level explanation if readily available. Keep it as adjacent compliance-practice evidence only; do not infer any 2019/8575 or 9281 non-compliance from it."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

------------------------------------------------------------------------
-- WrongType / attribution boundaries.
------------------------------------------------------------------------

data FirstNineEqualsSpringview : Set where
data SameConsultantEqualsIndependentProducer : Set where
data NearbyKoalaUseEqualsRealisedSpringviewConnectivity : Set where
data RehabilitatedAreaEqualsImmediateOffsetEquivalence : Set where
data AdjacentProjectNonComplianceEqualsCurrentProjectNonCompliance : Set where
data TwoNonCompliancesEqualsKnownConditionIdentity : Set where

firstNineDoesNotBecomeSpringview : FirstNineEqualsSpringview → ⊥
firstNineDoesNotBecomeSpringview ()

sameConsultantDoesNotCreateIndependence : SameConsultantEqualsIndependentProducer → ⊥
sameConsultantDoesNotCreateIndependence ()

nearbyUseDoesNotCreateSpringviewConnectivity : NearbyKoalaUseEqualsRealisedSpringviewConnectivity → ⊥
nearbyUseDoesNotCreateSpringviewConnectivity ()

rehabilitationDoesNotCreateImmediateEquivalence : RehabilitatedAreaEqualsImmediateOffsetEquivalence → ⊥
rehabilitationDoesNotCreateImmediateEquivalence ()

adjacentNonComplianceDoesNotTransfer : AdjacentProjectNonComplianceEqualsCurrentProjectNonCompliance → ⊥
adjacentNonComplianceDoesNotTransfer ()

summaryCountDoesNotIdentifyConditions : TwoNonCompliancesEqualsKnownConditionIdentity → ⊥
summaryCountDoesNotIdentifyConditions ()

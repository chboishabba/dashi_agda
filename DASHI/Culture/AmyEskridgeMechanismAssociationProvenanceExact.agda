module DASHI.Culture.AmyEskridgeMechanismAssociationProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact as Amy
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as Gravity

------------------------------------------------------------------------
-- AMY MECHANISM-ASSOCIATION PROVENANCE
--
-- Membership in the existing cross-pollinated chart is not, by itself, a
-- source-entitled statement that Amy Eskridge named or endorsed that exact
-- modern mechanism family.  Until an exact Amy carrier/segment is supplied,
-- chart membership is classified as DASHI contextual reconstruction.
------------------------------------------------------------------------

data MechanismAssociationStatus : Set where
  amySourceEntitledAssociation : MechanismAssociationStatus
  dashiContextualReconstruction : MechanismAssociationStatus
  associationUnresolved : MechanismAssociationStatus

record MechanismAssociationReceipt : Set where
  constructor mechanism-association-receipt
  field
    mechanism : Gravity.MechanismFamily
    status : MechanismAssociationStatus
    provenanceNote : String
    exactAmySourceLocator : String

open MechanismAssociationReceipt public

contextualAssociation : Gravity.MechanismFamily → String → MechanismAssociationReceipt
contextualAssociation mechanism note =
  mechanism-association-receipt
    mechanism
    dashiContextualReconstruction
    note
    ""

liTorrAssociation : MechanismAssociationReceipt
liTorrAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.coherentSuperconductorGravity
    Amy.canonicalEskridgeMechanismChart)
  "DASHI cross-pollination associates the Amy/POAMS historical lane with the Li-Torr coherent-superconductor gravity family; no exact Amy source segment is asserted here for that ontology identity"

podkletnovAssociation : MechanismAssociationReceipt
podkletnovAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.superconductingWeightAnomaly
    Amy.canonicalEskridgeMechanismChart)
  "DASHI contextual mechanism-family association; exact Amy source entitlement remains unresolved"

impulsiveAssociation : MechanismAssociationReceipt
impulsiveAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.impulsiveSuperconductorMomentum
    Amy.canonicalEskridgeMechanismChart)
  "DASHI contextual mechanism-family association; exact Amy source entitlement remains unresolved"

electrohydrodynamicAssociation : MechanismAssociationReceipt
electrohydrodynamicAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.highVoltageMomentumAlternative
    Amy.canonicalEskridgeMechanismChart)
  "DASHI ordinary-physics/confounder association; not an Amy-source-entitled antigravity claim"

woodwardAssociation : MechanismAssociationReceipt
woodwardAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.machianInertialVariation
    Amy.canonicalEskridgeMechanismChart)
  "DASHI contextual mechanism-family association; exact Amy source entitlement remains unresolved"

metricAssociation : MechanismAssociationReceipt
metricAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.negativeMassOrMetricLane
    Amy.canonicalEskridgeMechanismChart)
  "DASHI contextual metric-engineering comparison lane; exact Amy source entitlement remains unresolved"

------------------------------------------------------------------------
-- No contextual receipt can be silently promoted into source entitlement.
------------------------------------------------------------------------

data AmyMechanismSourceEntitlementPermission : Set where

contextualAssociationDoesNotCreateAmySourceEntitlement :
  AmyMechanismSourceEntitlementPermission → ⊥
contextualAssociationDoesNotCreateAmySourceEntitlement ()

record AmyMechanismAssociationBoundary : Set where
  constructor amy-mechanism-association-boundary
  field
    chartMembershipEqualsAmySourceEntitlement : Bool
    physicsPaperAttributionRetroactivelyCreatesAmyStatement : Bool
    contextualMechanismMayGuideReverseSearch : Bool
    exactAmySourceRequiredForAmyEntitledMechanismClaim : Bool
    unresolvedAssociationMayBeGuessed : Bool

canonicalAmyMechanismAssociationBoundary : AmyMechanismAssociationBoundary
canonicalAmyMechanismAssociationBoundary =
  amy-mechanism-association-boundary false false true true false

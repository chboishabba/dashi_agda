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
-- modern mechanism family. Exact HAL5 deck coordinates may entitle the narrow
-- historical proposition that Amy presented/discussed a mechanism family; they
-- do not entitle endorsement, experimental confirmation, or a modern DASHI
-- reinterpretation.
------------------------------------------------------------------------

data MechanismAssociationStatus : Set where
  amySourceEntitledAssociation : MechanismAssociationStatus
  dashiContextualReconstruction : MechanismAssociationStatus
  associationUnresolved : MechanismAssociationStatus

data AmySourceLocatorStatus : Set where
  exactAmySourceLocator : String → AmySourceLocatorStatus
  amySourceLocatorUnresolved : AmySourceLocatorStatus

record MechanismAssociationReceipt : Set where
  constructor mechanism-association-receipt
  field
    mechanism : Gravity.MechanismFamily
    status : MechanismAssociationStatus
    provenanceNote : String
    sourceLocatorStatus : AmySourceLocatorStatus

open MechanismAssociationReceipt public

contextualAssociation : Gravity.MechanismFamily → String → MechanismAssociationReceipt
contextualAssociation mechanism note =
  mechanism-association-receipt
    mechanism
    dashiContextualReconstruction
    note
    amySourceLocatorUnresolved

sourceEntitledDiscussion :
  Gravity.MechanismFamily → String → String → MechanismAssociationReceipt
sourceEntitledDiscussion mechanism note locator =
  mechanism-association-receipt
    mechanism
    amySourceEntitledAssociation
    note
    (exactAmySourceLocator locator)

hal5Deck : String
hal5Deck = "https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf"

liTorrAssociation : MechanismAssociationReceipt
liTorrAssociation = sourceEntitledDiscussion
  (Amy.EskridgeMechanismChart.coherentSuperconductorGravity
    Amy.canonicalEskridgeMechanismChart)
  "Amy's HAL5 deck explicitly presents Ning Li & Doug Torr AC Gravity and describes a magnetic field applied to a superconductor aligning ion spins to produce gravitomagnetic and gravitoelectric effects; this entitles historical discussion only, not endorsement or validation"
  "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 24 / slide Ning Li & Doug Torr AC Gravity (1990's)"

podkletnovAssociation : MechanismAssociationReceipt
podkletnovAssociation = sourceEntitledDiscussion
  (Amy.EskridgeMechanismChart.superconductingWeightAnomaly
    Amy.canonicalEskridgeMechanismChart)
  "Amy's HAL5 deck explicitly presents the Podkletnov Effect as a rotating YBCO-superconductor gravity-shielding/weight-reduction claim and notes community criticism and near-replications; this records discussion of the claim, not acceptance of it"
  "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 26 / slide Podkletnov Effect (1990's - 2000's)"

-- Amy's deck separately discusses Claude Poher's discharge-of-YBCO propelling
-- force claim, but the existing `impulsiveSuperconductorMomentum` family is a
-- broader DASHI ontology. Keep that ontology association contextual until an
-- exact same-object bridge from the Poher slide to this family is supplied.
impulsiveAssociation : MechanismAssociationReceipt
impulsiveAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.impulsiveSuperconductorMomentum
    Amy.canonicalEskridgeMechanismChart)
  "HAL5 contains a Claude Poher YBCO-discharge propulsion slide, but the existing DASHI impulsive-superconductor-momentum family is broader; exact ontology identity remains unresolved"

-- The deck discusses Brown/electrogravitics, but the DASHI high-voltage
-- momentum alternative is intentionally an ordinary-physics/confounder family.
-- Do not retroactively attribute that modern classification to Amy.
electrohydrodynamicAssociation : MechanismAssociationReceipt
electrohydrodynamicAssociation = contextualAssociation
  (Amy.EskridgeMechanismChart.highVoltageMomentumAlternative
    Amy.canonicalEskridgeMechanismChart)
  "Amy discusses Brown/electrogravitics historically; DASHI's electrohydrodynamic/ordinary-force classification remains a modern contextual reconstruction rather than an Amy-attributed interpretation"

woodwardAssociation : MechanismAssociationReceipt
woodwardAssociation = sourceEntitledDiscussion
  (Amy.EskridgeMechanismChart.machianInertialVariation
    Amy.canonicalEskridgeMechanismChart)
  "Amy's HAL5 deck explicitly presents the Woodward/Mach Effect as a reactionless-thruster proposal and relates it to negative-mass spacetime engineering; this entitles historical discussion only"
  "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 23 / slide Woodward Effect/Mach Effect (1990)"

metricAssociation : MechanismAssociationReceipt
metricAssociation = sourceEntitledDiscussion
  (Amy.EskridgeMechanismChart.negativeMassOrMetricLane
    Amy.canonicalEskridgeMechanismChart)
  "Amy's HAL5 Woodward slide explicitly discusses large negative mass warping spacetime and traversable-wormhole/Alcubierre-drive framing; this supports the narrow historical negative-mass/metric association, not DASHI's modern constitutive theory"
  "HAL5-Dec2018-Talk-AntiGravity.pdf, PDF page 23 / Woodward Effect/Mach Effect slide"

------------------------------------------------------------------------
-- Source-entitled discussion is still not endorsement or physical authority.
------------------------------------------------------------------------

data AmyMechanismSourceEntitlementPermission : Set where
data AmyDiscussionCreatesEndorsement : Set where
data AmyDiscussionCreatesExperimentalValidation : Set where
data AmyDiscussionCreatesDASHIMechanismAuthorship : Set where

contextualAssociationDoesNotCreateAmySourceEntitlement :
  AmyMechanismSourceEntitlementPermission → ⊥
contextualAssociationDoesNotCreateAmySourceEntitlement ()

sourceEntitledDiscussionDoesNotCreateEndorsement :
  AmyDiscussionCreatesEndorsement → ⊥
sourceEntitledDiscussionDoesNotCreateEndorsement ()

sourceEntitledDiscussionDoesNotCreateValidation :
  AmyDiscussionCreatesExperimentalValidation → ⊥
sourceEntitledDiscussionDoesNotCreateValidation ()

sourceEntitledDiscussionDoesNotCreateDASHIAuthorship :
  AmyDiscussionCreatesDASHIMechanismAuthorship → ⊥
sourceEntitledDiscussionDoesNotCreateDASHIAuthorship ()

record AmyMechanismAssociationBoundary : Set where
  constructor amy-mechanism-association-boundary
  field
    chartMembershipEqualsAmySourceEntitlement : Bool
    physicsPaperAttributionRetroactivelyCreatesAmyStatement : Bool
    emptyStringMayEncodeUnknownSourceLocator : Bool
    contextualMechanismMayGuideReverseSearch : Bool
    exactAmySourceRequiredForAmyEntitledMechanismClaim : Bool
    sourceEntitledDiscussionEqualsEndorsement : Bool
    sourceEntitledDiscussionEqualsExperimentalValidation : Bool
    sourceEntitledDiscussionEqualsDASHIModernAuthorship : Bool
    unresolvedAssociationMayBeGuessed : Bool

canonicalAmyMechanismAssociationBoundary : AmyMechanismAssociationBoundary
canonicalAmyMechanismAssociationBoundary =
  amy-mechanism-association-boundary false false false true true false false false false

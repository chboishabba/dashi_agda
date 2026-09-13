module DASHI.Law.SensibLawWoogarooPreservationAcquisitionDemandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Law.SensibLawWoogarooPreservationLegalCutsetExact as Cutset
import DASHI.Law.SensibLawWoogarooPreservationSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- WOOGAROO PRESERVATION ACQUISITION DEMAND
--
-- This is not a generic request for "more evidence".  Each acquisition is
-- bound to one exact surviving legal consumer and says what source object would
-- actually move that consumer.
------------------------------------------------------------------------

data AcquisitionPriority : Set where
  priorityOne : AcquisitionPriority
  priorityTwo : AcquisitionPriority
  priorityThree : AcquisitionPriority
  priorityFour : AcquisitionPriority
  priorityFive : AcquisitionPriority

data AcquisitionKind : Set where
  cadastralFootprintJoin : AcquisitionKind
  ecologicalHabitatFunctionReceipt : AcquisitionKind
  threateningProcessChronology : AcquisitionKind
  statutoryApplicationOpinion : AcquisitionKind
  approvalDecisionRecord : AcquisitionKind
  exemptionAuthorityReceipt : AcquisitionKind
  permanentProtectionInitiation : AcquisitionKind

data AcquisitionState : Set where
  sourceOpen : AcquisitionState
  partialSourcePaid : AcquisitionState
  sourcePaidConsumerOpen : AcquisitionState
  consumerPaid : AcquisitionState

record PreservationAcquisition : Set where
  constructor preservation-acquisition
  field
    priority : AcquisitionPriority
    acquisitionKind : AcquisitionKind
    targetMechanism : Cutset.LegalMechanism
    exactDemand : String
    whyThisMovesConsumer : String
    currentState : AcquisitionState
    sourceOrResidualReference : String
    acquisitionAutomaticallyCreatesProtection : Bool
    acquisitionAutomaticallyCreatesProtectionIsFalse :
      acquisitionAutomaticallyCreatesProtection ≡ false

open PreservationAcquisition public

exactParcelHabitatJoin : PreservationAcquisition
exactParcelHabitatJoin = preservation-acquisition
  priorityOne
  cadastralFootprintJoin
  Cutset.qldNCASection13CriticalHabitat
  "Join exact lot/plan and referred-action polygons for Scenic, Peninsula and Springview to each project's own threatened-species, vegetation-community and habitat-function mapping."
  "The s 13, s 102, s 49 and EPBC consumers are all same-place consumers; catchment-scale or campaign-scale evidence cannot substitute for exact footprint identity."
  partialSourcePaid
  "Scenic federal documentation and Springview Council parcel/application records exist; full same-object project x cadastral x ecology join remains open."
  false refl

criticalHabitatFunctionReceipt : PreservationAcquisition
criticalHabitatFunctionReceipt = preservation-acquisition
  priorityTwo
  ecologicalHabitatFunctionReceipt
  Cutset.qldNCASection13CriticalHabitat
  "Obtain a source-bearing ecological opinion or authoritative dataset addressing whether the exact Woogaroo habitat is essential for conservation of a viable population of protected wildlife or a native-wildlife community under the Queensland statutory consumer."
  "Threatened-species presence or mapped habitat is not enough by itself; the missing coordinate is essential conservation function for the exact habitat."
  sourceOpen
  "NCA s 13 legal test is source-paid; Woogaroo-specific same-footprint application is not."
  false refl

interimOrderThreatChronology : PreservationAcquisition
interimOrderThreatChronology = preservation-acquisition
  priorityThree
  threateningProcessChronology
  Cutset.qldNCASection102InterimConservationOrder
  "Bind the exact proposed clearing/works, earliest lawful commencement date, outstanding approvals, vegetation-clearance sequence and affected habitat polygons to a dated threatening-process chronology."
  "An interim conservation order is valuable only while the threatening process can still be prohibited or controlled; delay matters here as timing, not as protection."
  sourceOpen
  "The user's project-delay observation is retained as a lead only; this owner has not yet attached the exact primary record proving that specific project delay. Scenic's recovered source presently proves only an extension of the public-comment period."
  false refl

planningExemptionAuthority : PreservationAcquisition
planningExemptionAuthority = preservation-acquisition
  priorityFour
  exemptionAuthorityReceipt
  Cutset.planningSchemeConstraint
  "Recover the exact legislative/master-planning provision on which Springview's koala-habitat exemption depends, its temporal scope, parcel scope, and whether later modifications remain within it."
  "Council's statement proves that an exemption was treated as operative, but the legal source and exact scope of that exception are the coordinates needed to test whether the exception is valid and still applies."
  sourceOpen
  "Ipswich City Council source states the development is considered exempted development despite the whole area being mapped koala habitat."
  false refl

natureRefugeInitiationPackage : PreservationAcquisition
natureRefugeInitiationPackage = preservation-acquisition
  priorityFive
  permanentProtectionInitiation
  Cutset.qldNCASection49CompulsoryNatureRefuge
  "After the parcel and critical-habitat receipts are paid, prepare the exact land description, conservation basis, ownership/tenure material and source bundle needed for a ministerial request to initiate the compulsory nature-refuge process."
  "This is the strongest currently identified Queensland path from ecological evidence toward enduring protective tenure, but it remains discretionary and procedurally separate from proving habitat value."
  sourcePaidConsumerOpen
  "Statutory mechanism is source-paid; Woogaroo-specific initiation and executive outcome remain open."
  false refl

------------------------------------------------------------------------
-- Highest-alpha order: first pay coordinates reused by several mechanisms.
------------------------------------------------------------------------

record AcquisitionOrderingBoundary : Set where
  constructor acquisition-ordering-boundary
  field
    exactPlaceBeforeStatutoryApplication : Bool
    habitatFunctionBeforeCriticalHabitatConclusion : Bool
    threateningProcessBeforeEmergencyOrderRequest : Bool
    exceptionSourceBeforeExceptionChallenge : Bool
    natureRefugeRequestBeforeNatureRefugeOutcome : Bool
    delayIsProtection : Bool

canonicalAcquisitionOrderingBoundary : AcquisitionOrderingBoundary
canonicalAcquisitionOrderingBoundary =
  acquisition-ordering-boundary true true true true true false

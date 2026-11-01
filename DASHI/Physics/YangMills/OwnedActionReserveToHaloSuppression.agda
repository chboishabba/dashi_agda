module DASHI.Physics.YangMills.OwnedActionReserveToHaloSuppression where

-- Conditional bridge for the halo-volume route.
--
-- This file deliberately does not claim that CMP 122 supplies an owned action
-- reserve.  The reserve is step-local: an RG step acts on its current
-- effective density, so a global partition of one undepleted fine Wilson
-- action would be a stronger and potentially source-incorrect requirement.
-- What is needed first is that a single scale-k operation cannot spend the
-- same reserved action factor twice.

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; openTarget )

record StepLocalActionReserve : Set₁ where
  field
    Scale : Set
    Configuration : Set
    Block : Set
    Plaquette : Set
    Operation : Set
    Component : Set

    ownedPlaquettes : Scale → Block → List Plaquette
    markedBlocks : Operation → List Block
    reservedFactor : Operation → Configuration → ℝ
    componentCharge : Operation → Component → ℝ
    totalComponentCharge : Operation → Configuration → ℝ

    -- The two source-facing obligations: allocation is disjoint inside the
    -- current expansion term and its reserved factor dominates the charges
    -- assigned to its components.  No cross-scale common-action assertion is
    -- made here.
    chargesFormDisjointAllocation : Operation → Set
    noWithinStepDoubleCharge : Operation → Set
    reserveLowerBound : ∀ op U →
      totalComponentCharge op U ≤ℝ reservedFactor op U

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus

open StepLocalActionReserve public

record HaloSuppressionBridge
  (reserve : StepLocalActionReserve) : Set₁ where
  open StepLocalActionReserve reserve
  field
    Polymer : Set
    ConfigurationOf : Polymer → StepLocalActionReserve.Configuration reserve
    operationOf : Polymer → StepLocalActionReserve.Operation reserve
    weightedSize : Polymer → ℝ
    effectiveLargeFieldRate : Polymer → ℝ

    -- This is the actual theorem to prove from the activity construction,
    -- halo compression, and the owned reserve.  It must account for every
    -- loss before animal enumeration is permitted.
    activitySuppressedExtensively : ∀ (Y : Polymer) → Set

    -- The conclusion is intentionally kept as an explicit comparison
    -- surface: no exponential algebra is postulated as source extraction.
    suppressionRateControlsVolume : ∀ (Y : Polymer) →
      effectiveLargeFieldRate Y ≤ℝ weightedSize Y

open HaloSuppressionBridge public

record HaloSuppressionSourceAudit : Set where
  field
    stepLocalActionReserveExtracted : Bool
    withinStepNoDoubleChargeExtracted : Bool
    reservedWilsonLowerBoundExtracted : Bool
    boundedHaloExtracted : Bool
    extensiveActivityEstimateExtracted : Bool

-- Present CMP 122 extraction establishes neither an action partition nor a
-- per-block reserve.  These false values prevent this reducer from being
-- mistaken for a P10/P11 discharge.
currentHaloSuppressionSourceAudit : HaloSuppressionSourceAudit
currentHaloSuppressionSourceAudit = record
  { stepLocalActionReserveExtracted = false
  ; withinStepNoDoubleChargeExtracted = false
  ; reservedWilsonLowerBoundExtracted = false
  ; boundedHaloExtracted = false
  ; extensiveActivityEstimateExtracted = false
  }

currentHaloSuppressionBridgeStatus : VerificationStatus
currentHaloSuppressionBridgeStatus = openTarget

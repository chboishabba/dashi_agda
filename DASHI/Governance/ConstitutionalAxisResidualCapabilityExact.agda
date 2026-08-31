module DASHI.Governance.ConstitutionalAxisResidualCapabilityExact where

------------------------------------------------------------------------
-- CONSTITUTIONAL AXES / RESIDUAL CAPABILITY CONTRACTION
--
-- A producer/application may choose a task consumer, but high-impact action
-- cannot thereby erase non-optional affected-party/governance coordinates.
-- Consumer-relative adequacy therefore remains distinct from legitimacy of the
-- consumer itself.  Critical unresolved residuals contract execution
-- capability rather than merely becoming advisory refinement notes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Non-optional constitutional axes for high-impact human-facing action.
------------------------------------------------------------------------

data ConstitutionalAxis : Set where
  affectedPartyRights
  wellbeing
  autonomyManipulation
  externality
  contestability
  : ConstitutionalAxis

data AxisCovered : ConstitutionalAxis → Set where
  rightsCovered : AxisCovered affectedPartyRights
  wellbeingCovered : AxisCovered wellbeing
  autonomyCovered : AxisCovered autonomyManipulation
  externalityCovered : AxisCovered externality
  contestabilityCovered : AxisCovered contestability

record ConstitutionalCoverage : Set where
  constructor constitutional-coverage
  field
    rights : AxisCovered affectedPartyRights
    welfare : AxisCovered wellbeing
    autonomy : AxisCovered autonomyManipulation
    externalities : AxisCovered externality
    contest : AxisCovered contestability

canonicalConstitutionalCoverage : ConstitutionalCoverage
canonicalConstitutionalCoverage =
  constitutional-coverage
    rightsCovered
    wellbeingCovered
    autonomyCovered
    externalityCovered
    contestabilityCovered

------------------------------------------------------------------------
-- Application-selected consumer remains a separate coordinate.
------------------------------------------------------------------------

data ApplicationConsumer : Set where
  engagementOnly administrativeEligibility missionPerformance : ApplicationConsumer

data ConsumerAdequate : ApplicationConsumer → Set where
  engagementAdequate : ConsumerAdequate engagementOnly
  administrativeAdequate : ConsumerAdequate administrativeEligibility
  missionAdequate : ConsumerAdequate missionPerformance

record HighImpactAdmission (consumer : ApplicationConsumer) : Set where
  constructor high-impact-admission
  field
    consumerAdequacy : ConsumerAdequate consumer
    constitutionalCoverage : ConstitutionalCoverage

-- Consumer adequacy alone has no constructor into HighImpactAdmission.

canonicalEngagementHighImpactAdmission : HighImpactAdmission engagementOnly
canonicalEngagementHighImpactAdmission =
  high-impact-admission engagementAdequate canonicalConstitutionalCoverage

------------------------------------------------------------------------
-- Residual uncertainty contracts consequential capability.
------------------------------------------------------------------------

data CriticalResidual : Set where
  criticalResolved criticalUnresolved : CriticalResidual

data CapabilityClass : Set where
  refineObserve reversibleLowImpact irreversibleHighImpact : CapabilityClass

data CapabilityAvailable : CriticalResidual → CapabilityClass → Set where
  resolvedRefine : CapabilityAvailable criticalResolved refineObserve
  resolvedReversible : CapabilityAvailable criticalResolved reversibleLowImpact
  resolvedIrreversible : CapabilityAvailable criticalResolved irreversibleHighImpact
  unresolvedRefine : CapabilityAvailable criticalUnresolved refineObserve
  unresolvedReversible : CapabilityAvailable criticalUnresolved reversibleLowImpact

unresolvedCriticalResidualBlocksIrreversibleCapability :
  CapabilityAvailable criticalUnresolved irreversibleHighImpact → ⊥
unresolvedCriticalResidualBlocksIrreversibleCapability ()

------------------------------------------------------------------------
-- Self-benefiting emergency claims do not self-authorise overrides.
------------------------------------------------------------------------

data ClaimSource : Set where
  agentSelfClaim independentExternalClaim : ClaimSource

data EmergencyEvidence : ClaimSource → Set where
  independentlyGroundedEmergency : EmergencyEvidence independentExternalClaim

data EmergencyOverrideAuthority : Set where
  externallyGrantedEmergencyOverride : EmergencyOverrideAuthority

record EmergencyOverrideReceipt : Set where
  constructor emergency-override-receipt
  field
    evidence : EmergencyEvidence independentExternalClaim
    authority : EmergencyOverrideAuthority

selfGeneratedClaimCannotSupplyIndependentEmergencyEvidence :
  EmergencyEvidence agentSelfClaim → ⊥
selfGeneratedClaimCannotSupplyIndependentEmergencyEvidence ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ConstitutionalAxisResidualCapabilityBoundary : Set where
  constructor constitutional-axis-residual-capability-boundary
  field
    consumerAdequacyImpliesLegitimateConsumerSelection : Bool
    consumerAdequacyImpliesLegitimateConsumerSelectionIsFalse :
      consumerAdequacyImpliesLegitimateConsumerSelection ≡ false
    highImpactConsumerMayOmitConstitutionalAxes : Bool
    highImpactConsumerMayOmitConstitutionalAxesIsFalse :
      highImpactConsumerMayOmitConstitutionalAxes ≡ false
    unresolvedCriticalResidualPreservesIrreversibleCapability : Bool
    unresolvedCriticalResidualPreservesIrreversibleCapabilityIsFalse :
      unresolvedCriticalResidualPreservesIrreversibleCapability ≡ false
    selfBenefitingClaimCreatesEmergencyOverride : Bool
    selfBenefitingClaimCreatesEmergencyOverrideIsFalse :
      selfBenefitingClaimCreatesEmergencyOverride ≡ false
    constitutionalCoverageSettlesSubstantiveMorality : Bool
    constitutionalCoverageSettlesSubstantiveMoralityIsFalse :
      constitutionalCoverageSettlesSubstantiveMorality ≡ false
    reading : String

canonicalConstitutionalAxisResidualCapabilityBoundary :
  ConstitutionalAxisResidualCapabilityBoundary
canonicalConstitutionalAxisResidualCapabilityBoundary =
  constitutional-axis-residual-capability-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    "High-impact admission cannot be reduced to an application-selected consumer: affected-party rights, wellbeing, autonomy/manipulation, externalities and contestability remain non-optional coverage obligations. Critical unresolved residuals remove irreversible autonomous capability while preserving refinement/reversible action. Self-benefiting emergency claims require independently sourced evidence and externally granted override authority."

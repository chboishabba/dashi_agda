module DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope as Maxwell
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress

------------------------------------------------------------------------
-- CASIMIR U(1) ACTION / METRIC-VARIATION MAX-CUT
--
-- The existing Cartan-field image receipt already compiles the non-abelian
-- bracket to zero.  That is necessary but does not by itself identify the
-- action, its normalization, or its metric variation with Maxwell theory.
--
-- The live Maxwell scope already isolates exactly those missing semantics.
-- This owner recuts the Casimir restriction leaf into the smallest reusable
-- same-object payments without manufacturing a physical action theorem.
------------------------------------------------------------------------

record CasimirRestrictedActionNormalizationPayment : Set₁ where
  field
    SelectedField : Set
    selectedLieValue : SelectedField → _

    fieldImage :
      U1Stress.CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue

    KillingNormalizationCarrier : Set
    killingFormAndChargeNormalization : KillingNormalizationCarrier

    FieldStrengthCarrier : Set
    restrictedFieldStrength : SelectedField → FieldStrengthCarrier
    maxwellFieldStrength : SelectedField → FieldStrengthCarrier
    sameRestrictedFieldStrength :
      ∀ field → restrictedFieldStrength field ≡ maxwellFieldStrength field

    CommonAction : Set
    restrictedYangMillsAction : SelectedField → CommonAction
    maxwellAction : SelectedField → CommonAction
    restrictedActionEqualsMaxwell :
      ∀ field → restrictedYangMillsAction field ≡ maxwellAction field

    reading : String

open CasimirRestrictedActionNormalizationPayment public

restrictedFieldBracketZeroFromActionPayment :
  (payment : CasimirRestrictedActionNormalizationPayment) →
  ∀ left right →
  _
restrictedFieldBracketZeroFromActionPayment payment =
  U1Stress.restrictedFieldBracketZero (fieldImage payment)

record CasimirRestrictedMetricVariationPayment
    (actionPayment : CasimirRestrictedActionNormalizationPayment) : Set₁ where
  field
    MetricPerturbation : Set
    VariationValue : Set

    restrictedYMMetricVariation :
      SelectedField actionPayment → MetricPerturbation → VariationValue
    maxwellMetricVariation :
      SelectedField actionPayment → MetricPerturbation → VariationValue

    restrictionCommutesWithMetricVariation :
      ∀ field perturbation →
      restrictedYMMetricVariation field perturbation
      ≡ maxwellMetricVariation field perturbation

    StressCarrier : Set
    stressFromRestrictedVariation :
      (SelectedField actionPayment → MetricPerturbation → VariationValue) → StressCarrier
    stressFromMaxwellVariation :
      (SelectedField actionPayment → MetricPerturbation → VariationValue) → StressCarrier

    restrictedVariationStressEqualsMaxwellStress :
      stressFromRestrictedVariation restrictedYMMetricVariation
      ≡ stressFromMaxwellVariation maxwellMetricVariation

    reading : String

open CasimirRestrictedMetricVariationPayment public

------------------------------------------------------------------------
-- Maxwell-scope cross-pollination.
--
-- The G2 Maxwell scope is not instantiated here: it is a separate global
-- closure lane.  Its sector-restriction vocabulary is reused only to justify
-- the decomposition into normalization, field-strength preservation, action
-- restriction, and sector-variation equality.
------------------------------------------------------------------------

maxwellScopeNamesSectorRestriction : Bool
maxwellScopeNamesSectorRestriction = true

maxwellScopeOwner : String
maxwellScopeOwner = "DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope"

data ZeroProbeActionAutomaticallyPaysPhysicalU1Restriction : Set where

zeroProbeActionDoesNotPayPhysicalRestriction :
  ZeroProbeActionAutomaticallyPaysPhysicalU1Restriction → ⊥
zeroProbeActionDoesNotPayPhysicalRestriction ()

data RemainingCasimirU1ActionRestrictionBlocker : Set where
  missingKillingFormAndChargeNormalization : RemainingCasimirU1ActionRestrictionBlocker
  missingSameRestrictedFieldStrengthIdentification : RemainingCasimirU1ActionRestrictionBlocker
  missingRestrictedYMMaxwellActionEquality : RemainingCasimirU1ActionRestrictionBlocker
  missingMetricVariationRestrictionCommutation : RemainingCasimirU1ActionRestrictionBlocker

firstActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
firstActionRestrictionBlocker = missingKillingFormAndChargeNormalization

secondActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
secondActionRestrictionBlocker = missingSameRestrictedFieldStrengthIdentification

thirdActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
thirdActionRestrictionBlocker = missingRestrictedYMMaxwellActionEquality

fourthActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
fourthActionRestrictionBlocker = missingMetricVariationRestrictionCommutation

record CasimirU1ActionVariationBoundary : Set where
  constructor casimir-u1-action-variation-boundary
  field
    cartesianU1FieldImageAndBracketCompilerConsumed : Bool
    maxwellSectorRestrictionScopeReused : Bool
    killingNormalizationSeparated : Bool
    fieldStrengthRestrictionSeparated : Bool
    actionEqualitySeparated : Bool
    metricVariationCommutationSeparated : Bool
    zeroProbeActionSurfacePaysPhysicalRestriction : Bool

open CasimirU1ActionVariationBoundary public

canonicalCasimirU1ActionVariationBoundary : CasimirU1ActionVariationBoundary
canonicalCasimirU1ActionVariationBoundary =
  casimir-u1-action-variation-boundary true true true true true true false

casimirU1ActionVariationReading : String
casimirU1ActionVariationReading =
  "After the selected field is attached to the canonical Cartan-U(1) image, bracket-zero is compiled by the existing U1 theorem and is no longer an independent payment. The remaining physical action/stress seam is split into four application-owned leaves: Killing-form/charge normalization, equality of the same restricted field strength with Maxwell field strength, equality of the restricted Yang-Mills and Maxwell actions, and commutation of the restriction with metric variation/stress construction. MaxwellGaugeFieldEquationScope already exposes the corresponding sector-restriction grammar. The repository's old zero-probe Yang-Mills action surfaces do not pay these physical leaves."

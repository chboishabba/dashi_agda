module DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope as Maxwell
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2Lie
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress
import DASHI.Physics.QuantumVacuum.CasimirU1InvariantPairingRestrictionExact as Pairing

------------------------------------------------------------------------
-- CASIMIR U(1) ACTION / METRIC-VARIATION MAX-CUT
--
-- The existing Cartan-field image receipt compiles the non-abelian bracket to
-- zero.  The live Ad-invariant SU(2) pairing also restricts exactly to ordinary
-- multiplication on that same Cartan axis.  Therefore neither bracket-zero nor
-- an additional Killing-form decomposition is an independent payment here.
--
-- The first remaining normalization payment is physical: the electromagnetic
-- charge/gauge-coupling convention and action prefactor on the SAME field.
------------------------------------------------------------------------

record CasimirRestrictedActionNormalizationPayment : Set₁ where
  field
    SelectedField : Set
    selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra

    fieldImage :
      U1Stress.CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue

    PhysicalChargeCouplingNormalization : Set
    physicalChargeCouplingNormalization : PhysicalChargeCouplingNormalization

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
  Bracket.lieBracket
    (selectedLieValue payment left)
    (selectedLieValue payment right)
  ≡ SU2Lie.lieZero
restrictedFieldBracketZeroFromActionPayment payment =
  U1Stress.restrictedFieldBracketZero (fieldImage payment)

invariantPairingRestrictionWitness : Pairing.CasimirU1InvariantPairingBoundary
invariantPairingRestrictionWitness = Pairing.canonicalCasimirU1InvariantPairingBoundary

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
  missingPhysicalChargeCouplingNormalization : RemainingCasimirU1ActionRestrictionBlocker
  missingSameRestrictedFieldStrengthIdentification : RemainingCasimirU1ActionRestrictionBlocker
  missingRestrictedYMMaxwellActionEquality : RemainingCasimirU1ActionRestrictionBlocker
  missingMetricVariationRestrictionCommutation : RemainingCasimirU1ActionRestrictionBlocker

firstActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
firstActionRestrictionBlocker = missingPhysicalChargeCouplingNormalization

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
    invariantPairingRestrictionConsumed : Bool
    independentKillingDecompositionRequired : Bool
    physicalChargeCouplingNormalizationSeparated : Bool
    fieldStrengthRestrictionSeparated : Bool
    actionEqualitySeparated : Bool
    metricVariationCommutationSeparated : Bool
    zeroProbeActionSurfacePaysPhysicalRestriction : Bool

open CasimirU1ActionVariationBoundary public

canonicalCasimirU1ActionVariationBoundary : CasimirU1ActionVariationBoundary
canonicalCasimirU1ActionVariationBoundary =
  casimir-u1-action-variation-boundary
    true true true false true true true true false

casimirU1ActionVariationReading : String
casimirU1ActionVariationReading =
  "After the selected field is attached to the canonical Cartan-U(1) image, bracket-zero is compiled by the existing U1 theorem. The live SU(2) Ad-invariant pairing is also proved to restrict as <embed a,embed b>=a*b, so no second Killing/trace decomposition is required. The remaining action/stress seam is: physical electromagnetic charge/gauge-coupling normalization and action prefactor; equality of the same restricted field strength with Maxwell field strength; equality of restricted Yang-Mills and Maxwell actions; and commutation with metric variation/stress construction. MaxwellGaugeFieldEquationScope supplies the matching sector-restriction grammar. Zero-probe action surfaces do not pay these physical leaves."

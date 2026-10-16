module DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope as Maxwell
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2Lie
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress
import DASHI.Physics.QuantumVacuum.CasimirU1InvariantPairingRestrictionExact as Pairing
import DASHI.Physics.QuantumVacuum.CasimirU1CurvatureRestrictionExact as Curvature
import DASHI.Physics.QuantumVacuum.CasimirU1QuadraticActionDensityExact as Density

------------------------------------------------------------------------
-- CASIMIR U(1) ACTION / METRIC-VARIATION MAX-CUT
--
-- The theorem-bearing Cartan reductions are already compiler-owned:
--
--   [A,A] = 0
--   <embed a,embed b>_SU2 = a*b
--   F=dA+[A,A] => F=dA
--   common-prefactor <F,F> => common-prefactor F_U1^2.
--
-- A proof-relevant action-density functional then lifts the final pointwise
-- equality to action equality.  Consequently restricted YM=Maxwell action is
-- not an independent theorem after those same-object inputs are attached.
------------------------------------------------------------------------

record CasimirRestrictedActionNormalizationPayment : Set₁ where
  field
    SelectedField : Set
    selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra

    fieldImage :
      U1Stress.CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue

    PhysicalChargeCouplingNormalization : Set
    physicalChargeCouplingNormalization : PhysicalChargeCouplingNormalization
    physicalActionPrefactor : ℝ

    curvatureFormula :
      Curvature.SameObjectCurvatureFormula SelectedField selectedLieValue

    exteriorCartanImage :
      Density.ExteriorCartanImageReceipt curvatureFormula

    densityFunctional :
      Density.DensityActionFunctional SelectedField

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

restrictedCurvatureIsAbelianExterior :
  (payment : CasimirRestrictedActionNormalizationPayment) →
  ∀ left right →
  Curvature.curvatureFieldStrength (curvatureFormula payment) left right
  ≡ Curvature.exteriorFieldStrength (curvatureFormula payment) left right
restrictedCurvatureIsAbelianExterior payment =
  Curvature.cartanCurvatureReducesToExterior
    (fieldImage payment)
    (curvatureFormula payment)

restrictedYMAction :
  (payment : CasimirRestrictedActionNormalizationPayment) →
  Density.ActionValue (densityFunctional payment)
restrictedYMAction payment =
  Density.restrictedYMActionFromDensity
    (densityFunctional payment)
    (physicalActionPrefactor payment)
    (curvatureFormula payment)

maxwellAction :
  (payment : CasimirRestrictedActionNormalizationPayment) →
  Density.ActionValue (densityFunctional payment)
maxwellAction payment =
  Density.maxwellActionFromDensity
    (densityFunctional payment)
    (physicalActionPrefactor payment)
    (exteriorCartanImage payment)

restrictedActionEqualsMaxwell :
  (payment : CasimirRestrictedActionNormalizationPayment) →
  restrictedYMAction payment ≡ maxwellAction payment
restrictedActionEqualsMaxwell payment =
  Density.restrictedYMActionEqualsMaxwellFromSameDensityFunctional
    (fieldImage payment)
    (curvatureFormula payment)
    (exteriorCartanImage payment)
    (densityFunctional payment)
    (physicalActionPrefactor payment)

invariantPairingRestrictionWitness : Pairing.CasimirU1InvariantPairingBoundary
invariantPairingRestrictionWitness = Pairing.canonicalCasimirU1InvariantPairingBoundary

curvatureRestrictionWitness : Curvature.CasimirU1CurvatureRestrictionBoundary
curvatureRestrictionWitness = Curvature.canonicalCasimirU1CurvatureRestrictionBoundary

quadraticDensityRestrictionWitness : Density.CasimirU1QuadraticDensityBoundary
quadraticDensityRestrictionWitness = Density.canonicalU1QuadraticDensityBoundary

------------------------------------------------------------------------
-- Metric variation remains a separate same-path payment.  Action equality at
-- one selected metric does not by itself identify derivatives under metric
-- perturbation.  The next max-cut is to reuse the repository's common tangent/
-- first-variation machinery rather than postulate a second stress equality.
------------------------------------------------------------------------

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
  missingSameObjectNondegenerateCurvatureFormulaAttachment : RemainingCasimirU1ActionRestrictionBlocker
  missingExteriorFieldStrengthCartanImage : RemainingCasimirU1ActionRestrictionBlocker
  missingSameObjectActionDensityFunctional : RemainingCasimirU1ActionRestrictionBlocker
  missingMetricVariationRestrictionCommutation : RemainingCasimirU1ActionRestrictionBlocker

firstActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
firstActionRestrictionBlocker = missingPhysicalChargeCouplingNormalization

secondActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
secondActionRestrictionBlocker = missingSameObjectNondegenerateCurvatureFormulaAttachment

thirdActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
thirdActionRestrictionBlocker = missingExteriorFieldStrengthCartanImage

fourthActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
fourthActionRestrictionBlocker = missingSameObjectActionDensityFunctional

fifthActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
fifthActionRestrictionBlocker = missingMetricVariationRestrictionCommutation

record CasimirU1ActionVariationBoundary : Set where
  constructor casimir-u1-action-variation-boundary
  field
    cartesianU1FieldImageAndBracketCompilerConsumed : Bool
    maxwellSectorRestrictionScopeReused : Bool
    invariantPairingRestrictionConsumed : Bool
    independentKillingDecompositionRequired : Bool
    cartesianCurvatureReductionCompilerConsumed : Bool
    quadraticActionDensityCompilerConsumed : Bool
    secondAbelianBracketProofRequired : Bool
    independentRestrictedYMMaxwellActionEqualityRequiredAfterInputs : Bool
    physicalChargeCouplingNormalizationSeparated : Bool
    nondegenerateCurvatureAttachmentSeparated : Bool
    exteriorFieldStrengthCartanImageSeparated : Bool
    sameObjectActionFunctionalSeparated : Bool
    metricVariationCommutationSeparated : Bool
    zeroProbeActionSurfacePaysPhysicalRestriction : Bool

open CasimirU1ActionVariationBoundary public

canonicalCasimirU1ActionVariationBoundary : CasimirU1ActionVariationBoundary
canonicalCasimirU1ActionVariationBoundary =
  casimir-u1-action-variation-boundary
    true true true false true true false false
    true true true true true false

casimirU1ActionVariationReading : String
casimirU1ActionVariationReading =
  "The Cartan-U(1) action algebra is compiler-saturated. Bracket-zero follows from the field image; the live SU(2) invariant pairing restricts as <embed a,embed b>=a*b; same-object F=dA+[A,A] reduces to F=dA; and the quadratic YM density therefore equals the Maxwell square for any common prefactor. A proof-relevant same-object density functional lifts that pointwise result to full restricted-YM=Maxwell action equality, so no additional equality theorem remains after the inputs are attached. The genuine inputs are now: physical electromagnetic coupling/action-prefactor normalization; the selected nondegenerate curvature formula; Cartan image of its exterior field strength; the real action integration/measure functional; then common metric-path/variation transport. MaxwellGaugeFieldEquationScope remains an obligation grammar only, and zero-curvature probe actions do not count as physical payment."

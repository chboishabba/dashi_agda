module DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope as Maxwell
import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as PathDerivative
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2Lie
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress
import DASHI.Physics.QuantumVacuum.CasimirU1InvariantPairingRestrictionExact as Pairing
import DASHI.Physics.QuantumVacuum.CasimirU1CurvatureRestrictionExact as Curvature
import DASHI.Physics.QuantumVacuum.CasimirU1QuadraticActionDensityExact as Density
import DASHI.Physics.QuantumVacuum.CasimirU1MetricVariationTransportExact as MetricTransport
import DASHI.Physics.QuantumVacuum.CasimirFreeMaxwellActionNormalizationExact as Normalization

------------------------------------------------------------------------
-- CASIMIR U(1) ACTION / METRIC-VARIATION MAX-CUT
--
-- The theorem-bearing Cartan reductions are compiler-owned:
--
--   [A,A] = 0
--   <embed a,embed b>_SU2 = a*b
--   F=dA+[A,A] => F=dA
--   common-prefactor <F,F> => common-prefactor F_U1^2
--   same density functional => S_YM|U1 = S_Maxwell
--   same action along same metric path => delta S_YM = delta S_Maxwell.
--
-- The common free-field action normalization is a same-object convention
-- payment, not a request for a measured CODATA alpha_EM value.  Empirical charge
-- calibration belongs to matter coupling / phenomenology and is separated.
------------------------------------------------------------------------

record CasimirRestrictedActionNormalizationPayment : Set₁ where
  field
    SelectedField : Set
    selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra

    fieldImage :
      U1Stress.CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue

    freeMaxwellNormalization :
      Normalization.FreeMaxwellActionNormalization

    curvatureFormula :
      Curvature.SameObjectCurvatureFormula SelectedField selectedLieValue

    exteriorCartanImage :
      Density.ExteriorCartanImageReceipt curvatureFormula

    densityFunctional :
      Density.DensityActionFunctional SelectedField

    reading : String

open CasimirRestrictedActionNormalizationPayment public

physicalActionPrefactor :
  CasimirRestrictedActionNormalizationPayment → ℝ
physicalActionPrefactor payment =
  Normalization.actionPrefactor (freeMaxwellNormalization payment)

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

metricVariationTransportWitness : MetricTransport.CasimirU1MetricVariationTransportBoundary
metricVariationTransportWitness = MetricTransport.canonicalU1MetricVariationTransportBoundary

freeMaxwellNormalizationWitness :
  Normalization.CasimirFreeMaxwellNormalizationBoundary
freeMaxwellNormalizationWitness =
  Normalization.canonicalFreeMaxwellNormalizationBoundary

------------------------------------------------------------------------
-- SAME-PATH METRIC VARIATION / COMMON STRESS READOUT
------------------------------------------------------------------------

record CasimirRestrictedMetricVariationPayment : Set₁ where
  field
    derivativeLaws : PathDerivative.SignedPathDerivativeLaws
    metricActionFamily : MetricTransport.SameMetricPathActionFamily
    commonStressReadout : MetricTransport.CommonStressReadout
    reading : String

open CasimirRestrictedMetricVariationPayment public

restrictedMetricVariationEqualsMaxwell :
  (payment : CasimirRestrictedMetricVariationPayment) →
  ∀ background perturbation →
  MetricTransport.restrictedYMMetricFirstVariation
    (derivativeLaws payment) (metricActionFamily payment)
    background perturbation
  ≡ MetricTransport.maxwellMetricFirstVariation
      (derivativeLaws payment) (metricActionFamily payment)
      background perturbation
restrictedMetricVariationEqualsMaxwell payment =
  MetricTransport.sameMetricPathActionEqualityImpliesVariationEquality
    (derivativeLaws payment)
    (metricActionFamily payment)

restrictedVariationCommonStressEqualsMaxwell :
  (payment : CasimirRestrictedMetricVariationPayment) →
  ∀ background perturbation →
  MetricTransport.stressFromFirstVariation (commonStressReadout payment)
    (MetricTransport.restrictedYMMetricFirstVariation
      (derivativeLaws payment) (metricActionFamily payment)
      background perturbation)
  ≡
  MetricTransport.stressFromFirstVariation (commonStressReadout payment)
    (MetricTransport.maxwellMetricFirstVariation
      (derivativeLaws payment) (metricActionFamily payment)
      background perturbation)
restrictedVariationCommonStressEqualsMaxwell payment background perturbation =
  MetricTransport.sameVariationImpliesSameCommonStressReadout
    (commonStressReadout payment)
    (restrictedMetricVariationEqualsMaxwell payment background perturbation)

maxwellScopeNamesSectorRestriction : Bool
maxwellScopeNamesSectorRestriction = true

maxwellScopeOwner : String
maxwellScopeOwner = "DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope"

data ZeroProbeActionAutomaticallyPaysPhysicalU1Restriction : Set where

zeroProbeActionDoesNotPayPhysicalRestriction :
  ZeroProbeActionAutomaticallyPaysPhysicalU1Restriction → ⊥
zeroProbeActionDoesNotPayPhysicalRestriction ()

data RemainingCasimirU1ActionRestrictionBlocker : Set where
  missingFreeMaxwellActionNormalization : RemainingCasimirU1ActionRestrictionBlocker
  missingSameObjectNondegenerateCurvatureFormulaAttachment : RemainingCasimirU1ActionRestrictionBlocker
  missingExteriorFieldStrengthCartanImage : RemainingCasimirU1ActionRestrictionBlocker
  missingSameObjectActionDensityFunctional : RemainingCasimirU1ActionRestrictionBlocker
  missingSameMetricPathActionFamily : RemainingCasimirU1ActionRestrictionBlocker
  missingMetricVariationStressReadout : RemainingCasimirU1ActionRestrictionBlocker

firstActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
firstActionRestrictionBlocker = missingFreeMaxwellActionNormalization

secondActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
secondActionRestrictionBlocker = missingSameObjectNondegenerateCurvatureFormulaAttachment

thirdActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
thirdActionRestrictionBlocker = missingExteriorFieldStrengthCartanImage

fourthActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
fourthActionRestrictionBlocker = missingSameObjectActionDensityFunctional

fifthActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
fifthActionRestrictionBlocker = missingSameMetricPathActionFamily

sixthActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
sixthActionRestrictionBlocker = missingMetricVariationStressReadout

record CasimirU1ActionVariationBoundary : Set where
  constructor casimir-u1-action-variation-boundary
  field
    cartesianU1FieldImageAndBracketCompilerConsumed : Bool
    maxwellSectorRestrictionScopeReused : Bool
    invariantPairingRestrictionConsumed : Bool
    independentKillingDecompositionRequired : Bool
    cartesianCurvatureReductionCompilerConsumed : Bool
    quadraticActionDensityCompilerConsumed : Bool
    metricVariationTransportCompilerConsumed : Bool
    freeMaxwellActionNormalizationInterfaceConsumed : Bool
    measuredAlphaEMRequiredForIdealCasimirActionWeld : Bool
    secondAbelianBracketProofRequired : Bool
    independentRestrictedYMMaxwellActionEqualityRequiredAfterInputs : Bool
    independentMetricVariationEqualityRequiredAfterSamePathActionEquality : Bool
    freeMaxwellNormalizationSeparated : Bool
    empiricalChargeCouplingCalibrationSeparate : Bool
    nondegenerateCurvatureAttachmentSeparated : Bool
    exteriorFieldStrengthCartanImageSeparated : Bool
    sameObjectActionFunctionalSeparated : Bool
    sameMetricPathActionFamilySeparated : Bool
    metricVariationStressReadoutSeparated : Bool
    zeroProbeActionSurfacePaysPhysicalRestriction : Bool

open CasimirU1ActionVariationBoundary public

canonicalCasimirU1ActionVariationBoundary : CasimirU1ActionVariationBoundary
canonicalCasimirU1ActionVariationBoundary =
  casimir-u1-action-variation-boundary
    true true true false true true true true false false false false
    true true true true true true true false

casimirU1ActionVariationReading : String
casimirU1ActionVariationReading =
  "The Cartan-U(1) action/variation algebra is compiler-saturated. Bracket-zero, invariant pairing, F=dA reduction, quadratic-density equality, common-density action equality and same-path first-variation equality are compiler output after their same-object inputs. The normalization input is now explicitly a FreeMaxwellActionNormalization: same physical field normalization, same generator/pairing convention and one common action prefactor. The ideal parallel-plate kernel does not require a measured alpha_EM payload; empirical charge/fine-structure calibration remains separate phenomenology. Remaining action inputs are selected nondegenerate curvature, Cartan image of its exterior field strength, real action integration/measure, one same metric-path action family, and the physical variation-to-stress readout."

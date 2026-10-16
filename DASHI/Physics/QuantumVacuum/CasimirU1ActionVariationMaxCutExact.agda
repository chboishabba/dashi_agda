module DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.MaxwellGaugeFieldEquationScope as Maxwell
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2Lie
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.QuantumVacuum.CasimirU1RestrictedSelectedQFTStressExact as U1Stress
import DASHI.Physics.QuantumVacuum.CasimirU1InvariantPairingRestrictionExact as Pairing
import DASHI.Physics.QuantumVacuum.CasimirU1CurvatureRestrictionExact as Curvature

------------------------------------------------------------------------
-- CASIMIR U(1) ACTION / METRIC-VARIATION MAX-CUT
--
-- Two algebraic reductions are already paid on the canonical Cartan axis:
--
--   [A,A] = 0
--   <embed a,embed b>_SU2 = a*b.
--
-- Moreover, whenever the SAME selected nondegenerate curvature object carries
-- F=dA+[A,A], the curvature compiler reduces it to F=dA.  The remaining
-- payments are therefore attachment/calibration/action/variation payments,
-- not new abelian Lie-algebra calculations.
------------------------------------------------------------------------

record CasimirRestrictedActionNormalizationPayment : Set₁ where
  field
    SelectedField : Set
    selectedLieValue : SelectedField → SU2Lie.SU2LieAlgebra

    fieldImage :
      U1Stress.CanonicalCartanU1FieldImageReceipt SelectedField selectedLieValue

    PhysicalChargeCouplingNormalization : Set
    physicalChargeCouplingNormalization : PhysicalChargeCouplingNormalization

    curvatureFormula :
      Curvature.SameObjectCurvatureFormula SelectedField selectedLieValue

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

restrictedCurvatureIsAbelianExterior :
  (payment : CasimirRestrictedActionNormalizationPayment) →
  ∀ left right →
  Curvature.curvatureFieldStrength (curvatureFormula payment) left right
  ≡ Curvature.exteriorFieldStrength (curvatureFormula payment) left right
restrictedCurvatureIsAbelianExterior payment =
  Curvature.cartanCurvatureReducesToExterior
    (fieldImage payment)
    (curvatureFormula payment)

invariantPairingRestrictionWitness : Pairing.CasimirU1InvariantPairingBoundary
invariantPairingRestrictionWitness = Pairing.canonicalCasimirU1InvariantPairingBoundary

curvatureRestrictionWitness : Curvature.CasimirU1CurvatureRestrictionBoundary
curvatureRestrictionWitness = Curvature.canonicalCasimirU1CurvatureRestrictionBoundary

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
  missingRestrictedYMMaxwellActionEquality : RemainingCasimirU1ActionRestrictionBlocker
  missingMetricVariationRestrictionCommutation : RemainingCasimirU1ActionRestrictionBlocker

firstActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
firstActionRestrictionBlocker = missingPhysicalChargeCouplingNormalization

secondActionRestrictionBlocker : RemainingCasimirU1ActionRestrictionBlocker
secondActionRestrictionBlocker = missingSameObjectNondegenerateCurvatureFormulaAttachment

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
    cartesianCurvatureReductionCompilerConsumed : Bool
    secondAbelianBracketProofRequired : Bool
    physicalChargeCouplingNormalizationSeparated : Bool
    nondegenerateCurvatureAttachmentSeparated : Bool
    actionEqualitySeparated : Bool
    metricVariationCommutationSeparated : Bool
    zeroProbeActionSurfacePaysPhysicalRestriction : Bool

open CasimirU1ActionVariationBoundary public

canonicalCasimirU1ActionVariationBoundary : CasimirU1ActionVariationBoundary
canonicalCasimirU1ActionVariationBoundary =
  casimir-u1-action-variation-boundary
    true true true false true false true true true true false

casimirU1ActionVariationReading : String
casimirU1ActionVariationReading =
  "The Cartan-U(1) algebraic reduction is now exhausted: bracket-zero is compiled from the field-image theorem; the live SU(2) invariant pairing restricts exactly as <embed a,embed b>=a*b; and any same-object curvature formula F=dA+[A,A] compiles to F=dA. The first remaining normalization leaf is physical electromagnetic charge/gauge-coupling/action-prefactor calibration. The next field-strength leaf is attachment of the real selected nondegenerate curvature formula, not another bracket calculation. After that remain restricted YM=Maxwell action equality and commutation with metric variation/stress construction. MaxwellGaugeFieldEquationScope supplies the matching sector-restriction grammar; zero-probe action surfaces do not pay these physical leaves."

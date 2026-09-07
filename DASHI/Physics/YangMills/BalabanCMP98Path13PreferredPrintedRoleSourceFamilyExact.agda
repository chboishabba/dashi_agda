{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PreferredPrintedRoleSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): PREFERRED SOURCE-CORRECT PRINTED-ROLE CUT
--
-- Preferred top-level payments:
--   1. selected Path13 variational/operator physical representation;
--   2. foundational Bishop -> legacy-real bridge;
--   3. printed CMP98 operator semantics on the selected chart:
--        dexpPlus, Jplus, Ad_exp, with pointwise inverse semantics;
--   4. scalar selected-cut threshold 1/24 <= r_cut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanR208BishopLegacyRingEmbeddingExact as R208Bridge
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedSemanticOperatorsExact as Printed
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedOperatorChartWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedRoleSourceFamilyExact as Source
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredDirectCalculusSourceFamilyExact as OldPreferred
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

selectedGeometry :
  ∀ {CoarseField} →
  OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField →
  Historical.Path13FamilyGeometry CoarseField
selectedGeometry representation =
  Geometry.asPath13FamilyGeometry
    (Geometry.canonicalReducedPath13FamilyGeometry
      (OperatorChart.selectedPhysical
        (OperatorChart.asSelectedPath13OperatorChartRepresentation representation)))

record SelectedPrintedOperatorSemantics
    {CoarseField : Set}
    (representation :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField) : Set₁ where
  field
    operators : Printed.PrintedSemanticOperators
    chartWeld : Weld.PrintedOperatorChartWeld
      (selectedGeometry representation) operators
open SelectedPrintedOperatorSemantics public

record PreferredPrintedRolePath13Inputs
    (CoarseField : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField

    bishopToLegacyReal : Bridge.BishopToDASHIRealBridge

    printedSemantics :
      SelectedPrintedOperatorSemantics selectedVariationalOperator

    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)
open PreferredPrintedRolePath13Inputs public

operatorChart :
  ∀ {CoarseField} → PreferredPrintedRolePath13Inputs CoarseField →
  OperatorChart.SelectedPath13OperatorChartRepresentation CoarseField
operatorChart inputs =
  OperatorChart.asSelectedPath13OperatorChartRepresentation
    (selectedVariationalOperator inputs)

asPrintedRoleInputs :
  ∀ {CoarseField} → PreferredPrintedRolePath13Inputs CoarseField →
  Source.PrintedRolePath13SourceFamilyInputs CoarseField
asPrintedRoleInputs inputs =
  let
    geometry = selectedGeometry (selectedVariationalOperator inputs)
    ops = operators (printedSemantics inputs)
    admission = RadiusPrincipal.path13RelativeContourInPrincipalImageFromOperatorChart
      (operatorChart inputs) (cutThreshold inputs)
  in record
    { Source.PrintedRolePath13SourceFamilyInputs.geometry = geometry
    ; Source.PrintedRolePath13SourceFamilyInputs.scalarEmbedding =
        R208Bridge.bishopBridgeRingEmbedding (bishopToLegacyReal inputs)
    ; Source.PrintedRolePath13SourceFamilyInputs.printedOperators = ops
    ; Source.PrintedRolePath13SourceFamilyInputs.relativeContourInPrincipalImage =
        admission
    ; Source.PrintedRolePath13SourceFamilyInputs.pointYRelevant =
        λ bond step point →
          Weld.principalPointYRelevant
            (chartWeld (printedSemantics inputs))
            (Historical.erasedRelativeContour geometry bond step point)
            (admission bond step point)
    }

preferredPrintedRolePath13Equation119QPrime :
  ∀ {CoarseField} → PreferredPrintedRolePath13Inputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Historical.Path13PositiveBond → Lie.SU2LieAlgebra
preferredPrintedRolePath13Equation119QPrime inputs =
  Source.printedRolePath13Equation119QPrime (asPrintedRoleInputs inputs)

preferredPrintedRolePath13Equation119QPrimeExact :
  ∀ {CoarseField}
    (inputs : PreferredPrintedRolePath13Inputs CoarseField)
    step perturbation bond →
  preferredPrintedRolePath13Equation119QPrime inputs step perturbation bond
  ≡ Source.printedRolePath13Equation119QPrime
      (asPrintedRoleInputs inputs) step perturbation bond
preferredPrintedRolePath13Equation119QPrimeExact inputs step perturbation bond = refl

fromOldPreferredR159 :
  ∀ {CoarseField} →
  OldPreferred.PreferredDirectCalculusPath13Inputs CoarseField →
  PreferredPrintedRolePath13Inputs CoarseField
fromOldPreferredR159 old = record
  { PreferredPrintedRolePath13Inputs.selectedVariationalOperator =
      OldPreferred.selectedVariationalOperator old
  ; PreferredPrintedRolePath13Inputs.bishopToLegacyReal =
      OldPreferred.bishopToLegacyReal old
  ; PreferredPrintedRolePath13Inputs.printedSemantics = record
      { SelectedPrintedOperatorSemantics.operators =
          Printed.fromR159UniformCalculus
            (OldPreferred.differentialCalculus old)
      ; SelectedPrintedOperatorSemantics.chartWeld =
          Weld.fromR159EverywhereRelevant
            (selectedGeometry (OldPreferred.selectedVariationalOperator old))
            (OldPreferred.differentialCalculus old)
      }
  ; PreferredPrintedRolePath13Inputs.cutThreshold =
      OldPreferred.cutThreshold old
  }

cmp98Path13PreferredPrintedRoleAdapterLevel : ProofLevel
cmp98Path13PreferredPrintedRoleAdapterLevel = machineChecked

cmp98Path13OldR159RouteCompatibilityLevel : ProofLevel
cmp98Path13OldR159RouteCompatibilityLevel = machineChecked

literalCMP98Path13PreferredPrintedRoleInputsLevel : ProofLevel
literalCMP98Path13PreferredPrintedRoleInputsLevel = conditional

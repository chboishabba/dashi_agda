{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PreferredT3MinimalScalarSourceFamilyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanR208BishopLegacyRingEmbeddingExact as BishopR208
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13T3SelectedPrintedSemanticsExact as T3Selected
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredPrintedRoleSourceFamilyExact as PrintedPreferred
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedRoleSourceFamilyExact as Source
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedOperatorChartWeldExact as Weld
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record PreferredT3MinimalScalarPath13Inputs
    (CoarseField Scalar : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField
    scalarEmbedding : R208.RationalRealRingEmbedding
    t3Semantics :
      T3Selected.SelectedT3PrintedSemantics
        {Scalar = Scalar} selectedVariationalOperator
    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)
open PreferredT3MinimalScalarPath13Inputs public

selectedGeometry :
  ∀ {CoarseField Scalar} →
  PreferredT3MinimalScalarPath13Inputs CoarseField Scalar →
  Historical.Path13FamilyGeometry CoarseField
selectedGeometry inputs =
  PrintedPreferred.selectedGeometry (selectedVariationalOperator inputs)

asPrintedRoleInputs :
  ∀ {CoarseField Scalar} →
  PreferredT3MinimalScalarPath13Inputs CoarseField Scalar →
  Source.PrintedRolePath13SourceFamilyInputs CoarseField
asPrintedRoleInputs inputs =
  let
    representation = selectedVariationalOperator inputs
    geometry = selectedGeometry inputs
    semantics = T3Selected.asSelectedPrintedOperatorSemantics (t3Semantics inputs)
    admission = RadiusPrincipal.path13RelativeContourInPrincipalImageFromOperatorChart
      (OperatorChart.asSelectedPath13OperatorChartRepresentation representation)
      (cutThreshold inputs)
  in record
    { Source.PrintedRolePath13SourceFamilyInputs.geometry = geometry
    ; Source.PrintedRolePath13SourceFamilyInputs.scalarEmbedding = scalarEmbedding inputs
    ; Source.PrintedRolePath13SourceFamilyInputs.printedOperators =
        PrintedPreferred.operators semantics
    ; Source.PrintedRolePath13SourceFamilyInputs.relativeContourInPrincipalImage = admission
    ; Source.PrintedRolePath13SourceFamilyInputs.pointYRelevant =
        λ bond step point →
          Weld.principalPointYRelevant
            (PrintedPreferred.chartWeld semantics)
            (Historical.erasedRelativeContour geometry bond step point)
            (admission bond step point)
    }

preferredT3MinimalScalarPath13Equation119QPrime :
  ∀ {CoarseField Scalar} →
  PreferredT3MinimalScalarPath13Inputs CoarseField Scalar →
  Nat → Perturbation.Path13RationalPerturbation →
  Historical.Path13PositiveBond → Lie.SU2LieAlgebra
preferredT3MinimalScalarPath13Equation119QPrime inputs =
  Source.printedRolePath13Equation119QPrime (asPrintedRoleInputs inputs)

preferredT3MinimalScalarPath13Equation119QPrimeExact :
  ∀ {CoarseField Scalar}
    (inputs : PreferredT3MinimalScalarPath13Inputs CoarseField Scalar)
    step perturbation bond →
  preferredT3MinimalScalarPath13Equation119QPrime inputs step perturbation bond
  ≡ Source.printedRolePath13Equation119QPrime
      (asPrintedRoleInputs inputs) step perturbation bond
preferredT3MinimalScalarPath13Equation119QPrimeExact inputs step perturbation bond = refl

fromBishopBridge :
  ∀ {CoarseField Scalar}
    (selected : OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField)
    (bridge : Bridge.BishopToDASHIRealBridge)
    (semantics : T3Selected.SelectedT3PrintedSemantics {Scalar = Scalar} selected)
    (threshold : RadiusPrincipal.Path13RadiusCutThreshold
      (OperatorChart.asSelectedPath13OperatorChartRepresentation selected)) →
  PreferredT3MinimalScalarPath13Inputs CoarseField Scalar
fromBishopBridge selected bridge semantics threshold = record
  { PreferredT3MinimalScalarPath13Inputs.selectedVariationalOperator = selected
  ; PreferredT3MinimalScalarPath13Inputs.scalarEmbedding =
      BishopR208.bishopBridgeRingEmbedding bridge
  ; PreferredT3MinimalScalarPath13Inputs.t3Semantics = semantics
  ; PreferredT3MinimalScalarPath13Inputs.cutThreshold = threshold
  }

cmp98Path13PreferredT3MinimalScalarAdapterLevel : ProofLevel
cmp98Path13PreferredT3MinimalScalarAdapterLevel = machineChecked

cmp98Path13BishopBridgeCompatibilityProducerLevel : ProofLevel
cmp98Path13BishopBridgeCompatibilityProducerLevel = machineChecked

literalCMP98Path13RationalRealRingEmbeddingLevel : ProofLevel
literalCMP98Path13RationalRealRingEmbeddingLevel = conditional

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PreferredDirectCalculusSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): PREFERRED DIRECT-CALCULUS SOURCE CUT
--
-- Preferred source payments:
--   1. selected Path13 variational/operator physical representation;
--   2. foundational Bishop -> legacy-real structural bridge;
--   3. R159.UniformAdjointDifferentialCalculus;
--   4. the scalar selected-cut threshold 1/24 <= r_cut.
--
-- Native radius, the R208 rational-real ring embedding, reduced/full geometry,
-- 74-link principal-image admission, and the Eq.(119) field family are compiler
-- outputs.  R177.ExistingFederbushConventionFamily is not a preferred payment.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanR208BishopLegacyRingEmbeddingExact as R208Bridge
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundOperatorChartExact as OperatorChart
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98Path13DirectCalculusSourceFamilyExact as Direct
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record PreferredDirectCalculusPath13Inputs
    (CoarseField : Set) : Set₁ where
  field
    selectedVariationalOperator :
      OperatorChart.SelectedPath13VariationalOperatorRepresentation CoarseField

    bishopToLegacyReal : Bridge.BishopToDASHIRealBridge

    differentialCalculus :
      R159.UniformAdjointDifferentialCalculus Lie.SU2LieAlgebra

    cutThreshold :
      RadiusPrincipal.Path13RadiusCutThreshold
        (OperatorChart.asSelectedPath13OperatorChartRepresentation
          selectedVariationalOperator)
open PreferredDirectCalculusPath13Inputs public

operatorChart :
  ∀ {CoarseField} → PreferredDirectCalculusPath13Inputs CoarseField →
  OperatorChart.SelectedPath13OperatorChartRepresentation CoarseField
operatorChart inputs =
  OperatorChart.asSelectedPath13OperatorChartRepresentation
    (selectedVariationalOperator inputs)

reducedGeometry :
  ∀ {CoarseField} → PreferredDirectCalculusPath13Inputs CoarseField →
  Geometry.ReducedPath13FamilyGeometry CoarseField
reducedGeometry inputs =
  Geometry.canonicalReducedPath13FamilyGeometry
    (OperatorChart.selectedPhysical (operatorChart inputs))

asDirectCalculusInputs :
  ∀ {CoarseField} → PreferredDirectCalculusPath13Inputs CoarseField →
  Direct.DirectCalculusPath13SourceFamilyInputs CoarseField
asDirectCalculusInputs inputs = record
  { Direct.DirectCalculusPath13SourceFamilyInputs.geometry =
      Geometry.asPath13FamilyGeometry (reducedGeometry inputs)
  ; Direct.DirectCalculusPath13SourceFamilyInputs.scalarEmbedding =
      R208Bridge.bishopBridgeRingEmbedding (bishopToLegacyReal inputs)
  ; Direct.DirectCalculusPath13SourceFamilyInputs.differentialCalculus =
      differentialCalculus inputs
  ; Direct.DirectCalculusPath13SourceFamilyInputs.relativeContourInPrincipalImage =
      RadiusPrincipal.path13RelativeContourInPrincipalImageFromOperatorChart
        (operatorChart inputs) (cutThreshold inputs)
  }

preferredPath13Equation119QPrime :
  ∀ {CoarseField} → PreferredDirectCalculusPath13Inputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Historical.Path13PositiveBond → Lie.SU2LieAlgebra
preferredPath13Equation119QPrime inputs =
  Direct.directCalculusPath13Equation119QPrime
    (asDirectCalculusInputs inputs)

preferredPath13Equation119QPrimeAtBondExact :
  ∀ {CoarseField}
    (inputs : PreferredDirectCalculusPath13Inputs CoarseField)
    step perturbation bond →
  preferredPath13Equation119QPrime inputs step perturbation bond
  ≡ Direct.directCalculusPath13Equation119QPrime
      (asDirectCalculusInputs inputs) step perturbation bond
preferredPath13Equation119QPrimeAtBondExact inputs step perturbation bond = refl

cmp98Path13PreferredDirectCalculusAdapterLevel : ProofLevel
cmp98Path13PreferredDirectCalculusAdapterLevel = machineChecked

cmp98Path13R177FederbushFamilyPrunedLevel : ProofLevel
cmp98Path13R177FederbushFamilyPrunedLevel = machineChecked

cmp98Path13NativeRadiusDerivedOnPreferredRouteLevel : ProofLevel
cmp98Path13NativeRadiusDerivedOnPreferredRouteLevel = machineChecked

cmp98Path13R208EmbeddingDerivedOnPreferredRouteLevel : ProofLevel
cmp98Path13R208EmbeddingDerivedOnPreferredRouteLevel = machineChecked

-- This owner changes the minimal source cut; it does not claim inhabitants for
-- any of the four preferred payments above.
literalCMP98Path13PreferredDirectCalculusInputsLevel : ProofLevel
literalCMP98Path13PreferredDirectCalculusInputsLevel = conditional

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): PATH13 TWO-CARRIER SOURCE FAMILY
--
-- This owner instantiates the generic two-carrier Eq.(119) compiler directly
-- on the physical side-13 perturbation field.  The remaining external inputs
-- are deliberately narrow:
--
--   * the selected variational Path13 background;
--   * one rational-real ring embedding;
--   * the already-owned Federbush convention family;
--   * one radius-six minus embedding for each selected positive coarse bond;
--   * principal-image admission of the literal erased relative contours.
--
-- Everything else is constructed: periodic realization, signed perturbation
-- projection, path adjoint transport, coarse segment, plus embedding,
-- translation law, relative contour, point Y_x, outer Y, g/Jminus/Ad operators,
-- selected-bond Eq.(119), and assembly over all positive coarse bonds.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Blocks
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119TwoCarrierSelectedBondExact as TwoCarrier
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanRationalUnitQuaternionRealLieAdjointExact as UnitAdjoint
import DASHI.Physics.YangMills.BalabanCMP98Equation119GeometryRelativeContourExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact as R163
import DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact as R162

Path13PositiveBond : Set
Path13PositiveBond = Carrier.PositiveBond Side13.side13

------------------------------------------------------------------------
-- Geometry/background data independent of the perturbation carrier.
------------------------------------------------------------------------

record Path13FamilyGeometry (CoarseField : Set) : Set₁ where
  field
    selectedPhysical :
      PathTarget.SelectedPhysicalBackground13Instantiation
        CoarseField Lie.SU2LieAlgebra

    minusEmbeddingFor :
      Path13PositiveBond → Nat →
      Embed.CenteredPeriodicNoWrapEmbedding
        R192.path13PeriodicIndex R158.sourceRadius

open Path13FamilyGeometry public

familyBackground :
  ∀ {CoarseField} → Path13FamilyGeometry CoarseField →
  Background.RationalSU2Background13
familyBackground geometry =
  PathTarget.path13Background (selectedPhysical geometry)

coarseSegmentFor : Path13PositiveBond → Contours.AxisSegment
coarseSegmentFor bond =
  R158.canonicalCoarseSegment
    (R182.carrierAxisToContourAxis (Carrier.second bond))
    Contours.positive

geometrySourceAt :
  ∀ {CoarseField} →
  Path13FamilyGeometry CoarseField → Path13PositiveBond →
  Geometry.Equation119GeometrySource
    R192.path13PeriodicIndex
    SU2.RationalUnitQuaternion
    Group.rationalSU2ExactLinkGroup
geometrySourceAt geometry bond = record
  { Geometry.Equation119GeometrySource.realization =
      λ _ → R192.path13PhysicalPeriodicRealization (familyBackground geometry)
  ; Geometry.Equation119GeometrySource.minusEmbedding =
      minusEmbeddingFor geometry bond
  ; Geometry.Equation119GeometrySource.coarseSegment =
      λ _ → coarseSegmentFor bond
  }

erasedRelativeContour :
  ∀ {CoarseField} →
  Path13FamilyGeometry CoarseField → Path13PositiveBond →
  Nat → Centered.CenteredBlockPoint4 6 → Q.RationalQuaternion
erasedRelativeContour geometry bond step point =
  R187.eraseUnitQuaternion
    (Geometry.relativeContourElement
      (geometrySourceAt geometry bond) step point)

path13PrincipalChart :
  ∀ {CoarseField} →
  Path13FamilyGeometry CoarseField →
  Log.StandardSU2PrincipalLogBall
    Lie.SU2LieAlgebra Q.RationalQuaternion ℚ
path13PrincipalChart geometry =
  Selected.principalChart
    (PathTarget.bridge13 (selectedPhysical geometry))

------------------------------------------------------------------------
-- Minimal remaining source inputs.
------------------------------------------------------------------------

record Path13TwoCarrierSourceFamilyInputs (CoarseField : Set) : Set₁ where
  field
    geometry : Path13FamilyGeometry CoarseField
    scalarEmbedding : R208.RationalRealRingEmbedding
    federbushConvention : R177.ExistingFederbushConventionFamily

    relativeContourInPrincipalImage :
      ∀ bond step point →
      Log.InPrincipalImage
        (path13PrincipalChart geometry)
        (erasedRelativeContour geometry bond step point)

open Path13TwoCarrierSourceFamilyInputs public

pointY :
  ∀ {CoarseField} →
  Path13TwoCarrierSourceFamilyInputs CoarseField →
  Path13PositiveBond → Nat → Centered.CenteredBlockPoint4 6 →
  Lie.SU2LieAlgebra
pointY inputs bond step point =
  Log.principalLog (path13PrincipalChart (geometry inputs))
    (erasedRelativeContour (geometry inputs) bond step point)

pointYExponentiatesToErasedRelativeContour :
  ∀ {CoarseField}
    (inputs : Path13TwoCarrierSourceFamilyInputs CoarseField)
    bond step point →
  Log.expSU2 (path13PrincipalChart (geometry inputs))
      (pointY inputs bond step point)
  ≡ erasedRelativeContour (geometry inputs) bond step point
pointYExponentiatesToErasedRelativeContour inputs bond step point =
  Log.expPrincipalLog
    (path13PrincipalChart (geometry inputs))
    (erasedRelativeContour (geometry inputs) bond step point)
    (relativeContourInPrincipalImage inputs bond step point)

scaledPointYTerms :
  ∀ {CoarseField} →
  Path13TwoCarrierSourceFamilyInputs CoarseField →
  Path13PositiveBond → Nat →
  List (Centered.CenteredBlockPoint4 6) →
  List Lie.SU2LieAlgebra
scaledPointYTerms inputs bond step [] = []
scaledPointYTerms inputs bond step (point ∷ points) =
  Perturbation.canonicalLocalScalarAction
    (R208.additive (scalarEmbedding inputs))
    R147.siteWeightℚ
    (pointY inputs bond step point)
  ∷ scaledPointYTerms inputs bond step points

outerY :
  ∀ {CoarseField} →
  Path13TwoCarrierSourceFamilyInputs CoarseField →
  Path13PositiveBond → Nat → Lie.SU2LieAlgebra
outerY inputs bond step =
  R146.sumV
    {C = R178.su2SignedCarrier}
    (scaledPointYTerms inputs bond step
      (Carrier.elements (Centered.centeredBlockFinite 6)))

path13Calculus :
  ∀ {CoarseField} →
  Path13TwoCarrierSourceFamilyInputs CoarseField →
  R159.UniformAdjointDifferentialCalculus Lie.SU2LieAlgebra
path13Calculus inputs =
  R177.asUniformAdjointDifferentialCalculus (federbushConvention inputs)

------------------------------------------------------------------------
-- Construct one selected-bond two-carrier source.
------------------------------------------------------------------------

sourceAt :
  ∀ {CoarseField} →
  Path13TwoCarrierSourceFamilyInputs CoarseField →
  Path13PositiveBond →
  TwoCarrier.TwoCarrierEquation119PathData
    R178.su2SignedCarrier
    Perturbation.Path13RationalPerturbation
    SU2.RationalUnitQuaternion
    R192.path13PeriodicIndex
    Group.rationalSU2ExactLinkGroup
sourceAt inputs bond = record
  { TwoCarrier.TwoCarrierEquation119PathData.realization =
      λ _ → R192.path13PhysicalPeriodicRealization
        (familyBackground (geometry inputs))

  ; TwoCarrier.TwoCarrierEquation119PathData.bondComponent =
      λ _ perturbation site direction →
        Perturbation.signedBondRealLie
          (R208.additive (scalarEmbedding inputs))
          (familyBackground (geometry inputs))
          perturbation site direction

  ; TwoCarrier.TwoCarrierEquation119PathData.adjointLink =
      λ _ → UnitAdjoint.unitAdjointRealLie (scalarEmbedding inputs)

  ; TwoCarrier.TwoCarrierEquation119PathData.scaleV =
      Perturbation.canonicalLocalScalarAction
        (R208.additive (scalarEmbedding inputs))

  ; TwoCarrier.TwoCarrierEquation119PathData.minusEmbedding =
      minusEmbeddingFor (geometry inputs) bond

  ; TwoCarrier.TwoCarrierEquation119PathData.plusEmbedding =
      λ step →
        R163.translatedEmbedding
          (minusEmbeddingFor (geometry inputs) bond step)
          (coarseSegmentFor bond)

  ; TwoCarrier.TwoCarrierEquation119PathData.coarseSegment =
      λ _ → coarseSegmentFor bond

  ; TwoCarrier.TwoCarrierEquation119PathData.coarseSegmentEndsAtPlusCentre =
      λ _ → refl

  ; TwoCarrier.TwoCarrierEquation119PathData.translationCommutation =
      R162.periodicSegmentCommutation R192.path13PeriodicIndex

  ; TwoCarrier.TwoCarrierEquation119PathData.dexpMinusOuter =
      λ step → R159.dexpMinusAt (path13Calculus inputs) (outerY inputs bond step)

  ; TwoCarrier.TwoCarrierEquation119PathData.inverseDexpMinusAt =
      λ step point →
        R159.jMinusAt (path13Calculus inputs) (pointY inputs bond step point)

  ; TwoCarrier.TwoCarrierEquation119PathData.adjointExpAt =
      λ step point →
        R159.adjointExp (path13Calculus inputs) (pointY inputs bond step point)

  ; TwoCarrier.TwoCarrierEquation119PathData.adjointExpOuter =
      λ step → R159.adjointExp (path13Calculus inputs) (outerY inputs bond step)
  }

path13TwoCarrierFieldFamily :
  ∀ {CoarseField} →
  Path13TwoCarrierSourceFamilyInputs CoarseField →
  TwoCarrier.TwoCarrierEquation119FieldFamily
    R178.su2SignedCarrier
    Perturbation.Path13RationalPerturbation
    Path13PositiveBond
    SU2.RationalUnitQuaternion
    R192.path13PeriodicIndex
    Group.rationalSU2ExactLinkGroup
path13TwoCarrierFieldFamily inputs = record
  { TwoCarrier.TwoCarrierEquation119FieldFamily.sourceAt = sourceAt inputs }

path13Equation119QPrime :
  ∀ {CoarseField} →
  Path13TwoCarrierSourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Path13PositiveBond → Lie.SU2LieAlgebra
path13Equation119QPrime inputs =
  TwoCarrier.assembledEquation119QPrime
    (path13TwoCarrierFieldFamily inputs)

path13Equation119QPrimeAtBondExact :
  ∀ {CoarseField}
    (inputs : Path13TwoCarrierSourceFamilyInputs CoarseField)
    step perturbation bond →
  path13Equation119QPrime inputs step perturbation bond
  ≡ TwoCarrier.selectedEquation119QPrime (sourceAt inputs bond) step perturbation
path13Equation119QPrimeAtBondExact inputs step perturbation bond = refl

cmp98Path13GeometryRelativeContourCompilerLevel : ProofLevel
cmp98Path13GeometryRelativeContourCompilerLevel = machineChecked

cmp98Path13PrincipalYCompilerLevel : ProofLevel
cmp98Path13PrincipalYCompilerLevel = machineChecked

cmp98Path13OuterYCompilerLevel : ProofLevel
cmp98Path13OuterYCompilerLevel = machineChecked

cmp98Path13TwoCarrierSourceFamilyCompilerLevel : ProofLevel
cmp98Path13TwoCarrierSourceFamilyCompilerLevel = machineChecked

cmp98Path13TwoCarrierFieldDerivativeCompilerLevel : ProofLevel
cmp98Path13TwoCarrierFieldDerivativeCompilerLevel = machineChecked

-- The only remaining Path13 source-family payments are now inhabitance of the
-- narrow input record above: selected Path13 variational background, scalar
-- ring embedding, per-bond centered minus embeddings, and principal-image
-- admission of the literal erased relative contours.  Federbush calculus itself
-- is consumed from the existing family rather than reproved.
literalCMP98Path13TwoCarrierSourceFamilyInputsLevel : ProofLevel
literalCMP98Path13TwoCarrierSourceFamilyInputsLevel = conditional

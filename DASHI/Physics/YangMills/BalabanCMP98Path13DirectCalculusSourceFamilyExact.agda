{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13DirectCalculusSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): DIRECT R159 DIFFERENTIAL-CALCULUS SOURCE FAMILY
--
-- The historical source owner accepts R177.ExistingFederbushConventionFamily,
-- but its Path13 consumer immediately forgets that stronger object and keeps
-- only R159.UniformAdjointDifferentialCalculus.  This owner exposes the actual
-- consumer boundary directly.
--
-- No new differential theorem is asserted here.  Existing R177 inputs remain
-- a compatibility route via R177.asUniformAdjointDifferentialCalculus.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119TwoCarrierSelectedBondExact as TwoCarrier
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanRationalUnitQuaternionRealLieAdjointExact as UnitAdjoint
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
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

record DirectCalculusPath13SourceFamilyInputs (CoarseField : Set) : Set₁ where
  field
    geometry : Historical.Path13FamilyGeometry CoarseField
    scalarEmbedding : R208.RationalRealRingEmbedding
    differentialCalculus : R159.UniformAdjointDifferentialCalculus Lie.SU2LieAlgebra
    relativeContourInPrincipalImage :
      ∀ bond step point →
      Log.InPrincipalImage
        (Historical.path13PrincipalChart geometry)
        (Historical.erasedRelativeContour geometry bond step point)
open DirectCalculusPath13SourceFamilyInputs public

pointY :
  ∀ {CoarseField} → DirectCalculusPath13SourceFamilyInputs CoarseField →
  Path13PositiveBond → Nat → Centered.CenteredBlockPoint4 6 → Lie.SU2LieAlgebra
pointY inputs bond step point =
  Log.principalLog (Historical.path13PrincipalChart (geometry inputs))
    (Historical.erasedRelativeContour (geometry inputs) bond step point)

scaledPointYTerms :
  ∀ {CoarseField} → DirectCalculusPath13SourceFamilyInputs CoarseField →
  Path13PositiveBond → Nat → List (Centered.CenteredBlockPoint4 6) →
  List Lie.SU2LieAlgebra
scaledPointYTerms inputs bond step [] = []
scaledPointYTerms inputs bond step (point ∷ points) =
  Perturbation.canonicalLocalScalarAction
    (R208.additive (scalarEmbedding inputs)) R147.siteWeightℚ
    (pointY inputs bond step point)
  ∷ scaledPointYTerms inputs bond step points

outerY :
  ∀ {CoarseField} → DirectCalculusPath13SourceFamilyInputs CoarseField →
  Path13PositiveBond → Nat → Lie.SU2LieAlgebra
outerY inputs bond step =
  R146.sumV {C = R178.su2SignedCarrier}
    (scaledPointYTerms inputs bond step
      (Carrier.elements (Centered.centeredBlockFinite 6)))

sourceAt :
  ∀ {CoarseField} →
  DirectCalculusPath13SourceFamilyInputs CoarseField → Path13PositiveBond →
  TwoCarrier.TwoCarrierEquation119PathData
    R178.su2SignedCarrier
    Perturbation.Path13RationalPerturbation
    SU2.RationalUnitQuaternion
    R192.path13PeriodicIndex
    Group.rationalSU2ExactLinkGroup
sourceAt inputs bond = record
  { TwoCarrier.TwoCarrierEquation119PathData.realization =
      λ _ → R192.path13PhysicalPeriodicRealization
        (Historical.familyBackground (geometry inputs))
  ; TwoCarrier.TwoCarrierEquation119PathData.bondComponent =
      λ _ perturbation site direction →
        Perturbation.signedBondRealLie
          (R208.additive (scalarEmbedding inputs))
          (Historical.familyBackground (geometry inputs))
          perturbation site direction
  ; TwoCarrier.TwoCarrierEquation119PathData.adjointLink =
      λ _ → UnitAdjoint.unitAdjointRealLie (scalarEmbedding inputs)
  ; TwoCarrier.TwoCarrierEquation119PathData.scaleV =
      Perturbation.canonicalLocalScalarAction
        (R208.additive (scalarEmbedding inputs))
  ; TwoCarrier.TwoCarrierEquation119PathData.minusEmbedding =
      Historical.minusEmbeddingFor (geometry inputs) bond
  ; TwoCarrier.TwoCarrierEquation119PathData.plusEmbedding =
      λ step → R163.translatedEmbedding
        (Historical.minusEmbeddingFor (geometry inputs) bond step)
        (Historical.coarseSegmentFor bond)
  ; TwoCarrier.TwoCarrierEquation119PathData.coarseSegment =
      λ _ → Historical.coarseSegmentFor bond
  ; TwoCarrier.TwoCarrierEquation119PathData.coarseSegmentEndsAtPlusCentre = λ _ → refl
  ; TwoCarrier.TwoCarrierEquation119PathData.translationCommutation =
      R162.periodicSegmentCommutation R192.path13PeriodicIndex
  ; TwoCarrier.TwoCarrierEquation119PathData.dexpMinusOuter =
      λ step → R159.dexpMinusAt (differentialCalculus inputs) (outerY inputs bond step)
  ; TwoCarrier.TwoCarrierEquation119PathData.inverseDexpMinusAt =
      λ step point → R159.jMinusAt (differentialCalculus inputs) (pointY inputs bond step point)
  ; TwoCarrier.TwoCarrierEquation119PathData.adjointExpAt =
      λ step point → R159.adjointExp (differentialCalculus inputs) (pointY inputs bond step point)
  ; TwoCarrier.TwoCarrierEquation119PathData.adjointExpOuter =
      λ step → R159.adjointExp (differentialCalculus inputs) (outerY inputs bond step)
  }

fieldFamily :
  ∀ {CoarseField} → DirectCalculusPath13SourceFamilyInputs CoarseField →
  TwoCarrier.TwoCarrierEquation119FieldFamily
    R178.su2SignedCarrier Perturbation.Path13RationalPerturbation
    Path13PositiveBond SU2.RationalUnitQuaternion
    R192.path13PeriodicIndex Group.rationalSU2ExactLinkGroup
fieldFamily inputs = record
  { TwoCarrier.TwoCarrierEquation119FieldFamily.sourceAt = sourceAt inputs }

directCalculusPath13Equation119QPrime :
  ∀ {CoarseField} → DirectCalculusPath13SourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Path13PositiveBond → Lie.SU2LieAlgebra
directCalculusPath13Equation119QPrime inputs =
  TwoCarrier.assembledEquation119QPrime (fieldFamily inputs)

directCalculusPath13Equation119QPrimeAtBondExact :
  ∀ {CoarseField} (inputs : DirectCalculusPath13SourceFamilyInputs CoarseField)
    step perturbation bond →
  directCalculusPath13Equation119QPrime inputs step perturbation bond
  ≡ TwoCarrier.selectedEquation119QPrime (sourceAt inputs bond) step perturbation
directCalculusPath13Equation119QPrimeAtBondExact inputs step perturbation bond = refl

fromHistoricalFederbush :
  ∀ {CoarseField} → Historical.Path13TwoCarrierSourceFamilyInputs CoarseField →
  DirectCalculusPath13SourceFamilyInputs CoarseField
fromHistoricalFederbush inputs = record
  { geometry = Historical.geometry inputs
  ; scalarEmbedding = Historical.scalarEmbedding inputs
  ; differentialCalculus =
      R177.asUniformAdjointDifferentialCalculus
        (Historical.federbushConvention inputs)
  ; relativeContourInPrincipalImage =
      Historical.relativeContourInPrincipalImage inputs
  }

cmp98Path13DirectCalculusSourceFamilyLevel : ProofLevel
cmp98Path13DirectCalculusSourceFamilyLevel = machineChecked

cmp98Path13HistoricalFederbushCompatibilityLevel : ProofLevel
cmp98Path13HistoricalFederbushCompatibilityLevel = machineChecked

-- Preferred source debt is one uniform exp/log differential calculus, not the
-- stronger R177 five-operator convention family.
literalCMP98UniformAdjointDifferentialCalculusLevel : ProofLevel
literalCMP98UniformAdjointDifferentialCalculusLevel = conditional

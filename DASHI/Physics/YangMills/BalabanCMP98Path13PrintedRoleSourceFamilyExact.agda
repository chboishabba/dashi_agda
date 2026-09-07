{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PrintedRoleSourceFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): DIRECT SOURCE-CORRECT PRINTED-ROLE FAMILY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Historical
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119TwoCarrierSelectedBondExact as TwoCarrier
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Perturbation
import DASHI.Physics.YangMills.BalabanRationalUnitQuaternionRealLieAdjointExact as UnitAdjoint
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP98Path13PrintedSemanticOperatorsExact as Printed
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact as R163
import DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact as R162

record PrintedRolePath13SourceFamilyInputs (CoarseField : Set) : Set₁ where
  field
    geometry : Historical.Path13FamilyGeometry CoarseField
    scalarEmbedding : R208.RationalRealRingEmbedding
    printedOperators : Printed.PrintedSemanticOperators

    relativeContourInPrincipalImage :
      ∀ bond step point →
      Log.InPrincipalImage
        (Historical.path13PrincipalChart geometry)
        (Historical.erasedRelativeContour geometry bond step point)

    pointYRelevant : ∀ bond step point →
      Printed.RelevantY printedOperators
        (Log.principalLog
          (Historical.path13PrincipalChart geometry)
          (Historical.erasedRelativeContour geometry bond step point))
open PrintedRolePath13SourceFamilyInputs public

pointY :
  ∀ {CoarseField} → PrintedRolePath13SourceFamilyInputs CoarseField →
  Historical.Path13PositiveBond → Nat → Centered.CenteredBlockPoint4 6 →
  Lie.SU2LieAlgebra
pointY inputs bond step point =
  Log.principalLog (Historical.path13PrincipalChart (geometry inputs))
    (Historical.erasedRelativeContour (geometry inputs) bond step point)

scaledPointYTerms :
  ∀ {CoarseField} → PrintedRolePath13SourceFamilyInputs CoarseField →
  Historical.Path13PositiveBond → Nat → List (Centered.CenteredBlockPoint4 6) →
  List Lie.SU2LieAlgebra
scaledPointYTerms inputs bond step [] = []
scaledPointYTerms inputs bond step (point ∷ points) =
  Perturbation.canonicalLocalScalarAction
    (R208.additive (scalarEmbedding inputs)) R147.siteWeightℚ
    (pointY inputs bond step point)
  ∷ scaledPointYTerms inputs bond step points

outerY :
  ∀ {CoarseField} → PrintedRolePath13SourceFamilyInputs CoarseField →
  Historical.Path13PositiveBond → Nat → Lie.SU2LieAlgebra
outerY inputs bond step =
  R146.sumV {C = R178.su2SignedCarrier}
    (scaledPointYTerms inputs bond step
      (Carrier.elements (Centered.centeredBlockFinite 6)))

jPlusAfterDexpPlusAtPointY :
  ∀ {CoarseField}
    (inputs : PrintedRolePath13SourceFamilyInputs CoarseField)
    bond step point vector →
  Printed.jPlus (printedOperators inputs) (pointY inputs bond step point)
    (Printed.dexpPlus (printedOperators inputs) (pointY inputs bond step point) vector)
  ≡ vector
jPlusAfterDexpPlusAtPointY inputs bond step point =
  Printed.jPlusAfterDexpPlus
    (printedOperators inputs)
    (pointY inputs bond step point)
    (pointYRelevant inputs bond step point)

sourceAt :
  ∀ {CoarseField} →
  PrintedRolePath13SourceFamilyInputs CoarseField →
  Historical.Path13PositiveBond →
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

  -- Historical public field names are retained by `TwoCarrier`, but the values
  -- are the source-correct printed CMP98 roles fixed by R148/R153.
  ; TwoCarrier.TwoCarrierEquation119PathData.dexpMinusOuter =
      λ step → Printed.dexpPlus (printedOperators inputs) (outerY inputs bond step)
  ; TwoCarrier.TwoCarrierEquation119PathData.inverseDexpMinusAt =
      λ step point → Printed.jPlus (printedOperators inputs) (pointY inputs bond step point)
  ; TwoCarrier.TwoCarrierEquation119PathData.adjointExpAt =
      λ step point → Printed.adjointExp (printedOperators inputs) (pointY inputs bond step point)
  ; TwoCarrier.TwoCarrierEquation119PathData.adjointExpOuter =
      λ step → Printed.adjointExp (printedOperators inputs) (outerY inputs bond step)
  }

fieldFamily :
  ∀ {CoarseField} → PrintedRolePath13SourceFamilyInputs CoarseField →
  TwoCarrier.TwoCarrierEquation119FieldFamily
    R178.su2SignedCarrier Perturbation.Path13RationalPerturbation
    Historical.Path13PositiveBond SU2.RationalUnitQuaternion
    R192.path13PeriodicIndex Group.rationalSU2ExactLinkGroup
fieldFamily inputs = record
  { TwoCarrier.TwoCarrierEquation119FieldFamily.sourceAt = sourceAt inputs }

printedRolePath13Equation119QPrime :
  ∀ {CoarseField} → PrintedRolePath13SourceFamilyInputs CoarseField →
  Nat → Perturbation.Path13RationalPerturbation →
  Historical.Path13PositiveBond → Lie.SU2LieAlgebra
printedRolePath13Equation119QPrime inputs =
  TwoCarrier.assembledEquation119QPrime (fieldFamily inputs)

cmp98Path13PrintedRoleSourceFamilyLevel : ProofLevel
cmp98Path13PrintedRoleSourceFamilyLevel = machineChecked

cmp98Path13PrintedPointInverseSemanticsLevel : ProofLevel
cmp98Path13PrintedPointInverseSemanticsLevel = machineChecked

literalCMP98Path13PrintedRoleSourceInputsLevel : ProofLevel
literalCMP98Path13PrintedRoleSourceInputsLevel = conditional

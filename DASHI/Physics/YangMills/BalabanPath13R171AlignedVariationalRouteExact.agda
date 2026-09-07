{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13R171AlignedVariationalRouteExact where

------------------------------------------------------------------------
-- PATH13: CHOOSE THE R171 OPERATOR DEFECT AS THE SELECTED/CUT DEFECT
--
-- The preferred source specialization can choose its defect algebra.  Choosing
-- the canonical adapter of the R171 operator kernel, and constructing the
-- principal-log cut with that same algebra, makes the later selected-cut /
-- operator-defect equality definitional.  The standard R171 representation
-- remains an authority input; the pointwise weld does not.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanR171OperatorKernelGroupDefectAdapterExact as Adapter
import DASHI.Physics.YangMills.BalabanCMP98SU2OperatorDefectFromPhysicalRadiusRound171Exact as R171
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Operator
import DASHI.Physics.YangMills.BalabanPath13VariationalSpecializationExact as Specialization
import DASHI.Physics.YangMills.BalabanPath13VariationalRadiusFromSpecializationExact as SpecializedRadius
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record R171AlignedPath13VariationalSource
    (CoarseField : Set) : Set₁ where
  field
    operatorRepresentation : R171.RationalSU2OperatorDefectRepresentation

    sourceTheorem :
      Variational.BackgroundFieldVariationalTheorem
        CoarseField Background.RationalSU2Background13
        Target.Path13PositiveBond ℚ

    chartRadius : ℚ
    PrincipalLogAdmissible : Q.RationalQuaternion → Set

    defectBelowRadiusImpliesAdmissible : ∀ value →
      Operator.defect (R171.kernel operatorRepresentation) value
      ≤ chartRadius →
      PrincipalLogAdmissible value

    principalChart :
      Log.StandardSU2PrincipalLogBall
        Lie.SU2LieAlgebra Q.RationalQuaternion ℚ

    operatorDefectMatchesSourceDeviation :
      ∀ coarse
        (small : Variational.CoarseSmallField sourceTheorem coarse)
        site axis →
      Operator.defect (R171.kernel operatorRepresentation)
        (Background.link
          (Variational.background sourceTheorem coarse small)
          axis site)
      ≡ Variational.bondDeviation sourceTheorem
          (Variational.bondValue sourceTheorem
            (Variational.background sourceTheorem coarse small)
            (pair site axis))
          (Variational.identityBondValue sourceTheorem)

    sourceOrderIsRationalOrder :
      Variational.LessEqual sourceTheorem ≡ _≤_

    sourceUpperBelowChartRadius :
      Selected.sourceFineBondUpper sourceTheorem ≤ chartRadius

    admissibleIsPrincipalImage :
      PrincipalLogAdmissible ≡ Log.InPrincipalImage principalChart

open R171AlignedPath13VariationalSource public

alignedCutData :
  ∀ {CoarseField} →
  R171AlignedPath13VariationalSource CoarseField →
  Path.PrincipalLogCutData Q.RationalQuaternion ℚ
alignedCutData source = record
  { Path.PrincipalLogCutData.defectAlgebra =
      Adapter.operatorKernelAsGroupDefectAlgebra
        (R171.kernel (operatorRepresentation source))
  ; Path.PrincipalLogCutData.chartRadius = chartRadius source
  ; Path.PrincipalLogCutData.PrincipalLogAdmissible =
      PrincipalLogAdmissible source
  ; Path.PrincipalLogCutData.defectBelowRadiusImpliesAdmissible =
      defectBelowRadiusImpliesAdmissible source
  }

asPath13VariationalSpecialization :
  ∀ {CoarseField} →
  R171AlignedPath13VariationalSource CoarseField →
  Specialization.Path13VariationalSpecialization
    CoarseField Lie.SU2LieAlgebra
asPath13VariationalSpecialization source = record
  { Specialization.Path13VariationalSpecialization.sourceTheorem =
      sourceTheorem source
  ; Specialization.Path13VariationalSpecialization.defectAlgebra =
      Adapter.operatorKernelAsGroupDefectAlgebra
        (R171.kernel (operatorRepresentation source))
  ; Specialization.Path13VariationalSpecialization.cutData = alignedCutData source
  ; Specialization.Path13VariationalSpecialization.principalChart =
      principalChart source
  ; Specialization.Path13VariationalSpecialization.physicalDefectMatchesSourceDeviation =
      operatorDefectMatchesSourceDeviation source
  ; Specialization.Path13VariationalSpecialization.sourceOrderIsChartOrder =
      sourceOrderIsRationalOrder source
  ; Specialization.Path13VariationalSpecialization.sameDefectAlgebra = refl
  ; Specialization.Path13VariationalSpecialization.sourceUpperBelowChartRadius =
      sourceUpperBelowChartRadius source
  ; Specialization.Path13VariationalSpecialization.admissibleIsPrincipalImage =
      admissibleIsPrincipalImage source
  }

record R171AlignedPath13PhysicalInputs
    (CoarseField : Set) : Set₁ where
  field
    alignedSource : R171AlignedPath13VariationalSource CoarseField
    coarse : CoarseField
    small : Variational.CoarseSmallField
      (sourceTheorem alignedSource) coarse

    sourceDeviationIsPhysicalInverseLinkNormSq : ∀ site axis →
      Variational.bondDeviation
        (sourceTheorem alignedSource)
        (Variational.bondValue
          (sourceTheorem alignedSource)
          (Variational.background (sourceTheorem alignedSource) coarse small)
          (pair site axis))
        (Variational.identityBondValue (sourceTheorem alignedSource))
      ≡ Norm.normSq
          (Telescope._-q_
            (Background.inverseLink13
              (Variational.background (sourceTheorem alignedSource) coarse small)
              axis site)
            Q.oneQ)

    sourceUpperBelowRelaxedRadius :
      Selected.sourceFineBondUpper (sourceTheorem alignedSource)
      ≤ Relaxed.fourRhoSquare

open R171AlignedPath13PhysicalInputs public

asRadiusNormalization :
  ∀ {CoarseField} →
  R171AlignedPath13PhysicalInputs CoarseField →
  SpecializedRadius.Path13VariationalRadiusNormalization CoarseField
asRadiusNormalization inputs = record
  { SpecializedRadius.Path13VariationalRadiusNormalization.specialization =
      asPath13VariationalSpecialization (alignedSource inputs)
  ; SpecializedRadius.Path13VariationalRadiusNormalization.coarse = coarse inputs
  ; SpecializedRadius.Path13VariationalRadiusNormalization.small = small inputs
  ; SpecializedRadius.Path13VariationalRadiusNormalization.sourceOrderIsRationalOrder =
      sourceOrderIsRationalOrder (alignedSource inputs)
  ; SpecializedRadius.Path13VariationalRadiusNormalization.sourceDeviationIsPhysicalInverseLinkNormSq =
      sourceDeviationIsPhysicalInverseLinkNormSq inputs
  ; SpecializedRadius.Path13VariationalRadiusNormalization.sourceUpperBelowRelaxedRadius =
      sourceUpperBelowRelaxedRadius inputs
  }

asSplitPath13PhysicalStandardRepresentation :
  ∀ {CoarseField} →
  R171AlignedPath13PhysicalInputs CoarseField →
  Split.SplitPath13PhysicalStandardRepresentation CoarseField
asSplitPath13PhysicalStandardRepresentation inputs = record
  { Split.SplitPath13PhysicalStandardRepresentation.physicalVariationalRadius =
      SpecializedRadius.asPath13SelectedVariationalRadiusRepresentation
        (asRadiusNormalization inputs)
  ; Split.SplitPath13PhysicalStandardRepresentation.standardOperatorRepresentation =
      operatorRepresentation (alignedSource inputs)
  ; Split.SplitPath13PhysicalStandardRepresentation.selectedCutDefectIsStandardOperatorDefect =
      λ value → refl
  }

selectedCutOperatorDefectEqualityIsDefinitional :
  ∀ {CoarseField}
    (inputs : R171AlignedPath13PhysicalInputs CoarseField)
    value →
  Path.defect
    (Path.defectAlgebra
      (Selected.cutData
        (Target.bridge13
          (SpecializedRadius.selected (asRadiusNormalization inputs)))))
    value
  ≡ Operator.defect
      (R171.kernel (operatorRepresentation (alignedSource inputs))) value
selectedCutOperatorDefectEqualityIsDefinitional inputs value = refl

r171AlignedPath13VariationalRouteLevel : ProofLevel
r171AlignedPath13VariationalRouteLevel = machineChecked

-- Standard R171 authority and the source/physical normalization facts remain
-- inputs; the old pointwise selected-cut/operator weld is compiler-owned here.
literalR171AlignedPath13PhysicalInputsLevel : ProofLevel
literalR171AlignedPath13PhysicalInputsLevel = conditional

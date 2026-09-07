{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13VariationalSpecializationExact where

------------------------------------------------------------------------
-- PATH13: SOURCE VARIATIONAL THEOREM -> LITERAL SELECTED BACKGROUND
--
-- The generic Bałaban variational theorem already chooses its background as a
-- function of the coarse field and source small-field proof.  When that theorem
-- is specialized directly to the literal Path13 fine-field carrier, there is no
-- reason to pay a second equality saying that the selected background is the
-- Path13 background: define the physical background to be that source-selected
-- object.  Likewise define the selected bond-group value to be the literal
-- Path13 link of that same background.
--
-- This compiler therefore makes the two old same-object fields
--
--   selectedBackgroundIsPath13
--   selectedBondGroupIsPath13Link
--
-- definitional.  The remaining inputs are the genuine representation/chart
-- identifications needed to connect the source theorem to the principal-log
-- defect language.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale

record Path13VariationalSpecialization
    (CoarseField Lie : Set) : Set₁ where
  field
    sourceTheorem :
      Variational.BackgroundFieldVariationalTheorem
        CoarseField Background.RationalSU2Background13
        Target.Path13PositiveBond ℚ

    defectAlgebra : Path.GroupDefectAlgebra Q.RationalQuaternion ℚ
    cutData : Path.PrincipalLogCutData Q.RationalQuaternion ℚ
    principalChart :
      Log.StandardSU2PrincipalLogBall Lie Q.RationalQuaternion ℚ

    physicalDefectMatchesSourceDeviation :
      ∀ coarse
        (small : Variational.CoarseSmallField sourceTheorem coarse)
        site axis →
      Path.defect defectAlgebra
        (Background.link
          (Variational.background sourceTheorem coarse small)
          axis site)
      ≡ Variational.bondDeviation sourceTheorem
          (Variational.bondValue sourceTheorem
            (Variational.background sourceTheorem coarse small)
            (pair site axis))
          (Variational.identityBondValue sourceTheorem)

    sourceOrderIsChartOrder :
      Variational.LessEqual sourceTheorem
      ≡ Scale.LessEqual (Path.scale defectAlgebra)

    sameDefectAlgebra : Path.defectAlgebra cutData ≡ defectAlgebra

    sourceUpperBelowChartRadius :
      Scale.LessEqual (Path.scale defectAlgebra)
        (Selected.sourceFineBondUpper sourceTheorem)
        (Path.chartRadius cutData)

    admissibleIsPrincipalImage :
      Path.PrincipalLogAdmissible cutData
      ≡ Log.InPrincipalImage principalChart

open Path13VariationalSpecialization public

selectedBondValue :
  ∀ {CoarseField Lie} →
  Path13VariationalSpecialization CoarseField Lie →
  (coarse : CoarseField) →
  Variational.CoarseSmallField
    (sourceTheorem _) coarse →
  Target.Path13PositiveBond → Q.RationalQuaternion
selectedBondValue specialization coarse small (pair site axis) =
  Background.link
    (Variational.background (sourceTheorem specialization) coarse small)
    axis site

asSelectedVariationalChartBridge :
  ∀ {CoarseField Lie} →
  (specialization : Path13VariationalSpecialization CoarseField Lie) →
  Selected.SelectedBackgroundVariationalChartBridge
    CoarseField Background.RationalSU2Background13
    Target.Path13PositiveBond Lie Q.RationalQuaternion ℚ
asSelectedVariationalChartBridge specialization = record
  { Selected.SelectedBackgroundVariationalChartBridge.variational =
      sourceTheorem specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.defectAlgebra =
      defectAlgebra specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.cutData =
      cutData specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.principalChart =
      principalChart specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.selectedBondGroup =
      selectedBondValue specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.defectMatchesPublishedBondDeviation =
      λ coarse small (pair site axis) →
        physicalDefectMatchesSourceDeviation specialization
          coarse small site axis
  ; Selected.SelectedBackgroundVariationalChartBridge.variationalOrderIsChartOrder =
      sourceOrderIsChartOrder specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.sameDefectAlgebra =
      sameDefectAlgebra specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.publishedUpperBelowChartRadius =
      sourceUpperBelowChartRadius specialization
  ; Selected.SelectedBackgroundVariationalChartBridge.admissibleIsPrincipalImage =
      admissibleIsPrincipalImage specialization
  }

selectedPhysicalBackground13 :
  ∀ {CoarseField Lie}
    (specialization : Path13VariationalSpecialization CoarseField Lie)
    (coarse : CoarseField)
    (small : Variational.CoarseSmallField
      (sourceTheorem specialization) coarse) →
  Target.SelectedPhysicalBackground13Instantiation CoarseField Lie
selectedPhysicalBackground13 specialization coarse small = record
  { Target.SelectedPhysicalBackground13Instantiation.bridge13 =
      asSelectedVariationalChartBridge specialization
  ; Target.SelectedPhysicalBackground13Instantiation.coarse13 = coarse
  ; Target.SelectedPhysicalBackground13Instantiation.small13 = small
  ; Target.SelectedPhysicalBackground13Instantiation.path13Background =
      Variational.background (sourceTheorem specialization) coarse small
  ; Target.SelectedPhysicalBackground13Instantiation.selectedBackgroundIsPath13 = refl
  ; Target.SelectedPhysicalBackground13Instantiation.selectedBondGroupIsPath13Link =
      λ site axis → refl
  }

selectedBackgroundEqualityIsDefinitional :
  ∀ {CoarseField Lie}
    (specialization : Path13VariationalSpecialization CoarseField Lie)
    (coarse : CoarseField)
    (small : Variational.CoarseSmallField
      (sourceTheorem specialization) coarse) →
  Selected.selectedBackground
    (Target.bridge13 (selectedPhysicalBackground13 specialization coarse small))
    coarse small
  ≡ Target.path13Background
      (selectedPhysicalBackground13 specialization coarse small)
selectedBackgroundEqualityIsDefinitional specialization coarse small = refl

selectedBondEqualityIsDefinitional :
  ∀ {CoarseField Lie}
    (specialization : Path13VariationalSpecialization CoarseField Lie)
    (coarse : CoarseField)
    (small : Variational.CoarseSmallField
      (sourceTheorem specialization) coarse)
    site axis →
  Selected.selectedBondGroup
    (Target.bridge13 (selectedPhysicalBackground13 specialization coarse small))
    coarse small (pair site axis)
  ≡ Background.link
      (Target.path13Background
        (selectedPhysicalBackground13 specialization coarse small))
      axis site
selectedBondEqualityIsDefinitional specialization coarse small site axis = refl

path13VariationalSpecializationCompilerLevel : ProofLevel
path13VariationalSpecializationCompilerLevel = machineChecked

-- The source theorem and source/chart representation identifications remain
-- genuine inputs.  This module removes only redundant same-object receipts.
literalPath13VariationalSourceSpecializationLevel : ProofLevel
literalPath13VariationalSourceSpecializationLevel = conditional

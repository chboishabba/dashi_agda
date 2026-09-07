{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13VariationalRadiusFromSpecializationExact where

------------------------------------------------------------------------
-- PATH13: SOURCE SPECIALIZATION -> PHYSICAL VARIATIONAL/RADIUS RECORD
--
-- Once the generic Bałaban theorem has been specialized directly to the
-- literal Path13 carrier, the selected physical object is compiler output.
-- This owner shows that the larger historical
-- `Path13SelectedVariationalRadiusRepresentation` needs only three remaining
-- normalization facts:
--
--   source order = rational order;
--   source bond deviation = physical inverse-link norm-square defect;
--   source fine-bond upper <= the configured relaxed radius.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath13VariationalSpecializationExact as Specialization
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as Radius
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record Path13VariationalRadiusNormalization
    (CoarseField : Set) : Set₁ where
  field
    specialization :
      Specialization.Path13VariationalSpecialization
        CoarseField Lie.SU2LieAlgebra

    coarse : CoarseField
    small : Variational.CoarseSmallField
      (Specialization.sourceTheorem specialization) coarse

    sourceOrderIsRationalOrder :
      Variational.LessEqual (Specialization.sourceTheorem specialization)
      ≡ _≤_

    sourceDeviationIsPhysicalInverseLinkNormSq : ∀ site axis →
      Variational.bondDeviation
        (Specialization.sourceTheorem specialization)
        (Variational.bondValue
          (Specialization.sourceTheorem specialization)
          (Variational.background
            (Specialization.sourceTheorem specialization) coarse small)
          (pair site axis))
        (Variational.identityBondValue
          (Specialization.sourceTheorem specialization))
      ≡ Norm.normSq
          (Telescope._-q_
            (Background.inverseLink13
              (Variational.background
                (Specialization.sourceTheorem specialization) coarse small)
              axis site)
            Q.oneQ)

    sourceUpperBelowRelaxedRadius :
      Selected.sourceFineBondUpper
        (Specialization.sourceTheorem specialization)
      ≤ Relaxed.fourRhoSquare

open Path13VariationalRadiusNormalization public

selected :
  ∀ {CoarseField} →
  Path13VariationalRadiusNormalization CoarseField →
  Target.SelectedPhysicalBackground13Instantiation
    CoarseField Lie.SU2LieAlgebra
selected normalization =
  Specialization.selectedPhysicalBackground13
    (specialization normalization)
    (coarse normalization)
    (small normalization)

selectedChartOrderIsRationalOrder :
  ∀ {CoarseField}
    (normalization : Path13VariationalRadiusNormalization CoarseField) →
  Scale.LessEqual
    (Path.scale
      (Selected.defectAlgebra (Target.bridge13 (selected normalization))))
  ≡ _≤_
selectedChartOrderIsRationalOrder normalization =
  trans
    (sym
      (Specialization.sourceOrderIsChartOrder
        (specialization normalization)))
    (sourceOrderIsRationalOrder normalization)

selectedDefectIsPhysicalInverseLinkNormSq :
  ∀ {CoarseField}
    (normalization : Path13VariationalRadiusNormalization CoarseField)
    site axis →
  Path.defect
    (Selected.defectAlgebra (Target.bridge13 (selected normalization)))
    (Selected.selectedBondGroup
      (Target.bridge13 (selected normalization))
      (Target.coarse13 (selected normalization))
      (Target.small13 (selected normalization))
      (pair site axis))
  ≡ Norm.normSq
      (Telescope._-q_
        (Background.inverseLink13
          (Target.path13Background (selected normalization)) axis site)
        Q.oneQ)
selectedDefectIsPhysicalInverseLinkNormSq normalization site axis =
  trans
    (Specialization.physicalDefectMatchesSourceDeviation
      (specialization normalization)
      (coarse normalization) (small normalization) site axis)
    (sourceDeviationIsPhysicalInverseLinkNormSq normalization site axis)

asPath13SelectedVariationalRadiusRepresentation :
  ∀ {CoarseField} →
  Path13VariationalRadiusNormalization CoarseField →
  Radius.Path13SelectedVariationalRadiusRepresentation CoarseField
asPath13SelectedVariationalRadiusRepresentation normalization = record
  { Radius.Path13SelectedVariationalRadiusRepresentation.selected =
      selected normalization
  ; Radius.Path13SelectedVariationalRadiusRepresentation.selectedOrderIsRationalOrder =
      selectedChartOrderIsRationalOrder normalization
  ; Radius.Path13SelectedVariationalRadiusRepresentation.selectedDefectIsPhysicalInverseLinkNormSq =
      selectedDefectIsPhysicalInverseLinkNormSq normalization
  ; Radius.Path13SelectedVariationalRadiusRepresentation.publishedUpperBelowRelaxedRadius =
      sourceUpperBelowRelaxedRadius normalization
  }

path13VariationalRadiusFromSpecializationLevel : ProofLevel
path13VariationalRadiusFromSpecializationLevel = machineChecked

literalPath13VariationalRadiusNormalizationLevel : ProofLevel
literalPath13VariationalRadiusNormalizationLevel = conditional

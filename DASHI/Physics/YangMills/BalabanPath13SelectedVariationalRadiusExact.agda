{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact where

------------------------------------------------------------------------
-- PATH13 SELECTED VARIATIONAL BACKGROUND -> NATIVE INVERSE-LINK RADIUS
--
-- The side-four selected-background owner already proves that the published
-- variational fine-bond estimate yields the physical inverse-link radius once
-- three same-object representation facts are fixed:
--
--   * the selected defect order is rational order;
--   * the selected defect on a physical link is N(U^-1 - 1);
--   * the published source upper is <= 4 rho^2.
--
-- This module performs the identical reduction on the literal side-13 carrier.
-- It does NOT construct the selected Path13 background or invent any of those
-- three physical-identification facts.  It proves that a separate
-- `SelectedInverseLinkRadius13` receipt is no longer needed once they are paid.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Target
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record Path13SelectedVariationalRadiusRepresentation
    (CoarseField : Set) : Set₁ where
  field
    selected : Target.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra

    selectedOrderIsRationalOrder :
      Scale.LessEqual
        (Path.scale (Selected.defectAlgebra (Target.bridge13 selected)))
      ≡ _≤_

    selectedDefectIsPhysicalInverseLinkNormSq : ∀ site axis →
      Path.defect
        (Selected.defectAlgebra (Target.bridge13 selected))
        (Selected.selectedBondGroup
          (Target.bridge13 selected)
          (Target.coarse13 selected)
          (Target.small13 selected)
          (pair site axis))
      ≡ Norm.normSq
          (Telescope._-q_
            (Background.inverseLink13
              (Target.path13Background selected) axis site)
            Q.oneQ)

    publishedUpperBelowRelaxedRadius :
      Selected.sourceFineBondUpper
        (Selected.variational (Target.bridge13 selected))
      ≤ Relaxed.fourRhoSquare

open Path13SelectedVariationalRadiusRepresentation public

selectedBondDefectBelowPublishedUpper :
  ∀ {CoarseField}
    (inputs : Path13SelectedVariationalRadiusRepresentation CoarseField)
    site axis →
  Path.defect
    (Selected.defectAlgebra (Target.bridge13 (selected inputs)))
    (Selected.selectedBondGroup
      (Target.bridge13 (selected inputs))
      (Target.coarse13 (selected inputs))
      (Target.small13 (selected inputs))
      (pair site axis))
  ≤ Selected.sourceFineBondUpper
      (Selected.variational (Target.bridge13 (selected inputs)))
selectedBondDefectBelowPublishedUpper inputs site axis =
  let
    chosen = selected inputs
    bridge = Target.bridge13 chosen
    theorem = Selected.variational bridge
    coarse = Target.coarse13 chosen
    small = Target.small13 chosen
    bond = pair site axis
    upper = Selected.sourceFineBondUpper theorem
    deviation =
      Variational.bondDeviation theorem
        (Variational.bondValue theorem
          (Variational.background theorem coarse small) bond)
        (Variational.identityBondValue theorem)

    sourceBound : Variational.LessEqual theorem deviation upper
    sourceBound = Variational.fineBondSmallness theorem coarse small bond

    chartBound :
      Scale.LessEqual (Path.scale (Selected.defectAlgebra bridge))
        deviation upper
    chartBound =
      subst
        (λ relation → relation deviation upper)
        (Selected.variationalOrderIsChartOrder bridge)
        sourceBound

    selectedBound :
      Scale.LessEqual (Path.scale (Selected.defectAlgebra bridge))
        (Path.defect (Selected.defectAlgebra bridge)
          (Selected.selectedBondGroup bridge coarse small bond))
        upper
    selectedBound =
      subst
        (λ lower →
          Scale.LessEqual (Path.scale (Selected.defectAlgebra bridge))
            lower upper)
        (sym (Selected.defectMatchesPublishedBondDeviation
          bridge coarse small bond))
        chartBound
  in
  subst
    (λ relation → relation
      (Path.defect (Selected.defectAlgebra bridge)
        (Selected.selectedBondGroup bridge coarse small bond))
      upper)
    (selectedOrderIsRationalOrder inputs)
    selectedBound

selectedPhysicalInverseLinkBelowPublishedUpper :
  ∀ {CoarseField}
    (inputs : Path13SelectedVariationalRadiusRepresentation CoarseField)
    site axis →
  Norm.normSq
    (Telescope._-q_
      (Background.inverseLink13
        (Target.path13Background (selected inputs)) axis site)
      Q.oneQ)
  ≤ Selected.sourceFineBondUpper
      (Selected.variational (Target.bridge13 (selected inputs)))
selectedPhysicalInverseLinkBelowPublishedUpper inputs site axis =
  subst
    (λ lower → lower ≤
      Selected.sourceFineBondUpper
        (Selected.variational (Target.bridge13 (selected inputs))))
    (selectedDefectIsPhysicalInverseLinkNormSq inputs site axis)
    (selectedBondDefectBelowPublishedUpper inputs site axis)

selectedPath13NativeRadius :
  ∀ {CoarseField} →
  Path13SelectedVariationalRadiusRepresentation CoarseField →
  Background.SelectedInverseLinkRadius13
    (Target.path13Background (selected _))
selectedPath13NativeRadius inputs = record
  { Background.SelectedInverseLinkRadius13.inverseLinkDefectBound =
      λ axis site →
        ℚP.≤-trans
          (selectedPhysicalInverseLinkBelowPublishedUpper inputs site axis)
          (publishedUpperBelowRelaxedRadius inputs)
  }

cmp98Path13SelectedVariationalRadiusCompilerLevel : ProofLevel
cmp98Path13SelectedVariationalRadiusCompilerLevel = machineChecked

-- Only the physical representation facts above remain inputs.  The radius
-- certificate itself is now compiler output.
literalCMP98Path13SelectedVariationalRadiusRepresentationLevel : ProofLevel
literalCMP98Path13SelectedVariationalRadiusRepresentationLevel = conditional

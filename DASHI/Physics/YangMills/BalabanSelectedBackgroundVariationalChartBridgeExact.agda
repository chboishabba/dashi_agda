module DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Compose the repository's source-faithful Bałaban variational theorem with
-- its SU(2) principal-log chart.  Once the physical bond deviation is
-- identified with the chart defect and the published source upper bound lies
-- below the selected chart radius, every selected background bond is admitted
-- to the principal branch.  Existence, regular-gauge membership, minimization,
-- uniqueness and inverse-orientation logarithms then share one background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale

sourceFineBondUpper :
  ∀ {CoarseField FineField Bond Bound}
    (theorem : Variational.BackgroundFieldVariationalTheorem
      CoarseField FineField Bond Bound) → Bound
sourceFineBondUpper theorem =
  Variational.multiply theorem (Variational.two theorem)
    (Variational.multiply theorem (Variational.B3 theorem)
      (Variational.multiply theorem (Variational.dimension theorem)
        (Variational.multiply theorem
          (Variational.power theorem
            (Variational.blockSide theorem)
            (Variational.multiply theorem
              (Variational.two theorem)
              (Variational.scaleDepth theorem)))
          (Variational.runningSmallness theorem))))

record SelectedBackgroundVariationalChartBridge
    (CoarseField FineField Bond Lie Group Bound : Set) : Set₁ where
  field
    variational :
      Variational.BackgroundFieldVariationalTheorem
        CoarseField FineField Bond Bound

    defectAlgebra : Path.GroupDefectAlgebra Group Bound
    cutData : Path.PrincipalLogCutData Group Bound
    principalChart : Log.StandardSU2PrincipalLogBall Lie Group Bound

    selectedBondGroup :
      (coarse : CoarseField) →
      Variational.CoarseSmallField variational coarse →
      Bond → Group

    defectMatchesPublishedBondDeviation :
      ∀ coarse small bond →
      Path.defect defectAlgebra (selectedBondGroup coarse small bond)
      ≡ Variational.bondDeviation variational
          (Variational.bondValue variational
            (Variational.background variational coarse small) bond)
          (Variational.identityBondValue variational)

    sameDefectAlgebra :
      Path.defectAlgebra cutData ≡ defectAlgebra

    publishedUpperBelowChartRadius :
      Scale.LessEqual (Path.scale defectAlgebra)
        (sourceFineBondUpper variational)
        (Path.chartRadius cutData)

    admissibleIsPrincipalImage : ∀ group →
      Path.PrincipalLogAdmissible cutData group
      ≡ Log.InPrincipalImage principalChart group

open SelectedBackgroundVariationalChartBridge public

selectedBackground :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    (coarse : CoarseField) →
  Variational.CoarseSmallField (variational bridge) coarse → FineField
selectedBackground bridge =
  Variational.background (variational bridge)

selectedBackgroundSatisfiesConstraint :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    coarse small →
  Variational.FineConstraint (variational bridge) coarse
    (selectedBackground bridge coarse small)
selectedBackgroundSatisfiesConstraint bridge =
  Variational.backgroundSatisfiesConstraint (variational bridge)

selectedBackgroundInRegularGauge :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    coarse small →
  Variational.FineRegularGauge (variational bridge)
    (selectedBackground bridge coarse small)
selectedBackgroundInRegularGauge bridge =
  Variational.backgroundInRegularGauge (variational bridge)

selectedBackgroundUniqueInRegularGauge :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    coarse small competitor →
  Variational.FineConstraint (variational bridge) coarse competitor →
  Variational.FineRegularGauge (variational bridge) competitor →
  Variational.action (variational bridge) competitor
    ≡ Variational.action (variational bridge)
        (selectedBackground bridge coarse small) →
  competitor ≡ selectedBackground bridge coarse small
selectedBackgroundUniqueInRegularGauge bridge =
  Variational.backgroundUnique (variational bridge)

selectedBackgroundBondDefectBelowChart :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    coarse small bond →
  Scale.LessEqual (Path.scale (defectAlgebra bridge))
    (Path.defect (defectAlgebra bridge)
      (selectedBondGroup bridge coarse small bond))
    (Path.chartRadius (cutData bridge))
selectedBackgroundBondDefectBelowChart bridge coarse small bond =
  let
    sourceBound =
      Variational.fineBondSmallness
        (variational bridge) coarse small bond

    defectBound :
      Scale.LessEqual (Path.scale (defectAlgebra bridge))
        (Path.defect (defectAlgebra bridge)
          (selectedBondGroup bridge coarse small bond))
        (sourceFineBondUpper (variational bridge))
    defectBound =
      subst
        (λ lower →
          Scale.LessEqual (Path.scale (defectAlgebra bridge)) lower
            (sourceFineBondUpper (variational bridge)))
        (sym (defectMatchesPublishedBondDeviation
          bridge coarse small bond))
        sourceBound
  in
  Scale.transitive (Path.scale (defectAlgebra bridge))
    defectBound
    (publishedUpperBelowChartRadius bridge)

selectedBackgroundBondPrincipalAdmissible :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    coarse small bond →
  Log.InPrincipalImage (principalChart bridge)
    (selectedBondGroup bridge coarse small bond)
selectedBackgroundBondPrincipalAdmissible bridge coarse small bond =
  let
    cutBound :
      Scale.LessEqual
        (Path.scale (Path.defectAlgebra (cutData bridge)))
        (Path.defect (Path.defectAlgebra (cutData bridge))
          (selectedBondGroup bridge coarse small bond))
        (Path.chartRadius (cutData bridge))
    cutBound =
      subst
        (λ selectedAlgebra →
          Scale.LessEqual (Path.scale selectedAlgebra)
            (Path.defect selectedAlgebra
              (selectedBondGroup bridge coarse small bond))
            (Path.chartRadius (cutData bridge)))
        (sym (sameDefectAlgebra bridge))
        (selectedBackgroundBondDefectBelowChart
          bridge coarse small bond)

    admissible :
      Path.PrincipalLogAdmissible (cutData bridge)
        (selectedBondGroup bridge coarse small bond)
    admissible =
      Path.defectBelowRadiusImpliesAdmissible (cutData bridge)
        (selectedBondGroup bridge coarse small bond)
        cutBound
  in
  subst
    (λ predicate →
      predicate (selectedBondGroup bridge coarse small bond))
    (admissibleIsPrincipalImage bridge
      (selectedBondGroup bridge coarse small bond))
    admissible

selectedBackgroundInverseLogOrientation :
  ∀ {CoarseField FineField Bond Lie Group Bound}
    (bridge : SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    coarse small bond →
  Log.principalLog (principalChart bridge)
    (Log.inverseGroup (principalChart bridge)
      (selectedBondGroup bridge coarse small bond))
  ≡ Log.negateLie (principalChart bridge)
      (Log.principalLog (principalChart bridge)
        (selectedBondGroup bridge coarse small bond))
selectedBackgroundInverseLogOrientation bridge coarse small bond =
  Log.principalLogOfInverse
    (principalChart bridge)
    (selectedBondGroup bridge coarse small bond)
    (selectedBackgroundBondPrincipalAdmissible
      bridge coarse small bond)

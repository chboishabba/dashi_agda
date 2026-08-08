module DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Fix the Round-33 variational/chart bridge to the literal side-four rational
-- SU(2) background carrier.  The published fine-bond estimate now produces
-- the exact relaxed inverse-link radius consumed by the physical gauge and
-- terminal-Hessian theorems.  Together with the positive-scalar chart theorem,
-- the same selected background has constraint satisfaction, regular-gauge
-- uniqueness, physical chart admission and inverse-orientation logarithms.
--
-- This removes the formerly independent radius premise from the terminal
-- Hessian theorem.  The remaining nontrivial Gate-I producer is the correlated
-- physical Wilson lower bound for the same background and perturbation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (PositiveBond)
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusPrincipalChartExact as Radius
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Coercivity
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as WilsonGlobal
import DASHI.Physics.YangMills.BalabanP33PhysicalTerminalHessianCoercivityExact as Terminal
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

PhysicalBond4 : Set
PhysicalBond4 = PositiveBond Path4.side4

record SelectedPhysicalBackgroundInstantiation
    (CoarseField Lie : Set) : Set₁ where
  field
    bridge : Selected.SelectedBackgroundVariationalChartBridge
      CoarseField Physical.RationalSU2Background4 PhysicalBond4
      Lie Q.RationalQuaternion ℚ

    chartOrderIsRationalOrder :
      Scale.LessEqual
        (Path.scale (Selected.defectAlgebra bridge))
      ≡ _≤_

    selectedBondGroupIsPhysicalLink :
      ∀ coarse small bond →
      Selected.selectedBondGroup bridge coarse small bond
      ≡ Physical.link
          (Selected.selectedBackground bridge coarse small) bond

    selectedDefectIsPhysicalInverseLinkNormSq :
      ∀ coarse small bond →
      Path.defect (Selected.defectAlgebra bridge)
        (Selected.selectedBondGroup bridge coarse small bond)
      ≡ Norm.normSq
          (Telescope._-q_
            (Physical.inverseLink
              (Selected.selectedBackground bridge coarse small) bond)
            Q.oneQ)

    publishedUpperBelowRelaxedRadius :
      Selected.sourceFineBondUpper (Selected.variational bridge)
      ≤ Relaxed.fourRhoSquare

    physicalConjugateIsChartInverse : ∀ value →
      Physical.quaternionConjugate value
      ≡ Log.inverseGroup (Selected.principalChart bridge) value

    positiveScalarInPrincipalImage : ∀ value →
      ℚ.0ℚ < Q.q0 value →
      Log.InPrincipalImage (Selected.principalChart bridge) value

open SelectedPhysicalBackgroundInstantiation public

selectedPositiveScalarChart :
  ∀ {CoarseField Lie} →
  SelectedPhysicalBackgroundInstantiation CoarseField Lie →
  Radius.RationalSU2PositiveScalarChart Lie
selectedPositiveScalarChart inputs = record
  { Radius.RationalSU2PositiveScalarChart.chart =
      Selected.principalChart (bridge inputs)
  ; Radius.RationalSU2PositiveScalarChart.physicalConjugateIsChartInverse =
      physicalConjugateIsChartInverse inputs
  ; Radius.RationalSU2PositiveScalarChart.positiveScalarInPrincipalImage =
      positiveScalarInPrincipalImage inputs
  }

selectedBackgroundDefectBelowPublishedUpper :
  ∀ {CoarseField Lie}
    (inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie)
    coarse small bond →
  Path.defect (Selected.defectAlgebra (bridge inputs))
    (Selected.selectedBondGroup (bridge inputs) coarse small bond)
  ≤ Selected.sourceFineBondUpper
      (Selected.variational (bridge inputs))
selectedBackgroundDefectBelowPublishedUpper inputs coarse small bond =
  let
    dataSet = bridge inputs
    theorem = Selected.variational dataSet
    upper = Selected.sourceFineBondUpper theorem
    deviation =
      Variational.bondDeviation theorem
        (Variational.bondValue theorem
          (Variational.background theorem coarse small) bond)
        (Variational.identityBondValue theorem)

    sourceBound =
      Variational.fineBondSmallness theorem coarse small bond

    sourceBoundInChartOrder :
      Scale.LessEqual
        (Path.scale (Selected.defectAlgebra dataSet))
        deviation upper
    sourceBoundInChartOrder =
      subst
        (λ relation → relation deviation upper)
        (Selected.variationalOrderIsChartOrder dataSet)
        sourceBound

    defectBoundInChartOrder :
      Scale.LessEqual
        (Path.scale (Selected.defectAlgebra dataSet))
        (Path.defect (Selected.defectAlgebra dataSet)
          (Selected.selectedBondGroup dataSet coarse small bond))
        upper
    defectBoundInChartOrder =
      subst
        (λ lower →
          Scale.LessEqual
            (Path.scale (Selected.defectAlgebra dataSet)) lower upper)
        (sym
          (Selected.defectMatchesPublishedBondDeviation
            dataSet coarse small bond))
        sourceBoundInChartOrder
  in
  subst
    (λ relation →
      relation
        (Path.defect (Selected.defectAlgebra dataSet)
          (Selected.selectedBondGroup dataSet coarse small bond))
        upper)
    (chartOrderIsRationalOrder inputs)
    defectBoundInChartOrder

selectedBackgroundRelaxedInverseLinkRadius :
  ∀ {CoarseField Lie}
    (inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie)
    coarse small →
  Relaxed.RelaxedInverseLinkRadius
    (Selected.selectedBackground (bridge inputs) coarse small)
selectedBackgroundRelaxedInverseLinkRadius inputs coarse small bond =
  let
    dataSet = bridge inputs
    upper = Selected.sourceFineBondUpper (Selected.variational dataSet)

    defectBelowUpper :
      Path.defect (Selected.defectAlgebra dataSet)
        (Selected.selectedBondGroup dataSet coarse small bond)
      ≤ upper
    defectBelowUpper =
      selectedBackgroundDefectBelowPublishedUpper
        inputs coarse small bond

    physicalDefectBelowUpper :
      Norm.normSq
        (Telescope._-q_
          (Physical.inverseLink
            (Selected.selectedBackground dataSet coarse small) bond)
          Q.oneQ)
      ≤ upper
    physicalDefectBelowUpper =
      subst
        (λ lower → lower ≤ upper)
        (selectedDefectIsPhysicalInverseLinkNormSq
          inputs coarse small bond)
        defectBelowUpper
  in
  ℚP.≤-trans
    physicalDefectBelowUpper
    (publishedUpperBelowRelaxedRadius inputs)

selectedBackgroundPhysicalLinkPrincipalImage :
  ∀ {CoarseField Lie}
    (inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie)
    coarse small bond →
  Log.InPrincipalImage
    (Selected.principalChart (bridge inputs))
    (Physical.link
      (Selected.selectedBackground (bridge inputs) coarse small) bond)
selectedBackgroundPhysicalLinkPrincipalImage inputs coarse small bond =
  Radius.relaxedRadiusImpliesPrincipalImage
    (selectedPositiveScalarChart inputs)
    (Selected.selectedBackground (bridge inputs) coarse small)
    (selectedBackgroundRelaxedInverseLinkRadius inputs coarse small)
    bond

selectedBridgeChartAdmissionIsOnPhysicalLink :
  ∀ {CoarseField Lie}
    (inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie)
    coarse small bond →
  Log.InPrincipalImage
    (Selected.principalChart (bridge inputs))
    (Physical.link
      (Selected.selectedBackground (bridge inputs) coarse small) bond)
selectedBridgeChartAdmissionIsOnPhysicalLink inputs coarse small bond =
  subst
    (λ value →
      Log.InPrincipalImage
        (Selected.principalChart (bridge inputs)) value)
    (selectedBondGroupIsPhysicalLink inputs coarse small bond)
    (Selected.selectedBackgroundBondPrincipalAdmissible
      (bridge inputs) coarse small bond)

selectedBackgroundPhysicalInverseLogOrientation :
  ∀ {CoarseField Lie}
    (inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie)
    coarse small bond →
  Log.principalLog (Selected.principalChart (bridge inputs))
    (Physical.inverseLink
      (Selected.selectedBackground (bridge inputs) coarse small) bond)
  ≡ Log.negateLie (Selected.principalChart (bridge inputs))
      (Log.principalLog (Selected.principalChart (bridge inputs))
        (Physical.link
          (Selected.selectedBackground (bridge inputs) coarse small) bond))
selectedBackgroundPhysicalInverseLogOrientation
    inputs coarse small bond =
  Radius.relaxedRadiusPhysicalInverseLogOrientation
    (selectedPositiveScalarChart inputs)
    (Selected.selectedBackground (bridge inputs) coarse small)
    (selectedBackgroundRelaxedInverseLinkRadius inputs coarse small)
    bond

------------------------------------------------------------------------
-- Remove the independent radius premise from the terminal Hessian theorem.
------------------------------------------------------------------------

record SelectedVariationalPerturbationFamily
    {CoarseField Lie Perturbation ConstraintIndex : Set}
    (inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie)
    (coarse : CoarseField)
    (small : Variational.CoarseSmallField
      (Selected.variational (bridge inputs)) coarse) : Set₁ where
  field
    model : Coercivity.SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex

    backgroundMatchesSelected : ∀ h →
      Coercivity.backgroundOf model h
      ≡ Selected.selectedBackground (bridge inputs) coarse small

open SelectedVariationalPerturbationFamily public

selectedVariationalRadiusAt :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (bridge inputs)) coarse}
    (family : SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h →
  Relaxed.RelaxedInverseLinkRadius
    (Coercivity.backgroundOf (model family) h)
selectedVariationalRadiusAt {inputs = inputs} {coarse} {small} family h =
  subst
    Relaxed.RelaxedInverseLinkRadius
    (sym (backgroundMatchesSelected family h))
    (selectedBackgroundRelaxedInverseLinkRadius inputs coarse small)

selectedVariationalTerminalCoefficient :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (bridge inputs)) coarse}
    (family : SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h →
  WilsonGlobal.PhysicalWilsonSignedLocal
    (Coercivity.backgroundOf (model family) h)
    (Coercivity.physicalFieldOf (model family) h) →
  Terminal.terminalPhysicalCoefficient
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation (model family) h)
selectedVariationalTerminalCoefficient family h local =
  Coercivity.selectedBackgroundLiteralHessianTerminalCoefficient
    (model family) h
    (selectedVariationalRadiusAt family h)
    local

selectedVariationalOneThirtySecond :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : SelectedPhysicalBackgroundInstantiation CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (bridge inputs)) coarse}
    (family : SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h →
  WilsonGlobal.PhysicalWilsonSignedLocal
    (Coercivity.backgroundOf (model family) h)
    (Coercivity.physicalFieldOf (model family) h) →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation (model family) h)
selectedVariationalOneThirtySecond family h local =
  Coercivity.selectedBackgroundLiteralHessianOneThirtySecond
    (model family) h
    (selectedVariationalRadiusAt family h)
    local

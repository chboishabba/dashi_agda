{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedLocalCStressCylinderExact where

------------------------------------------------------------------------
-- ONE SELECTED LOCAL-C CYLINDER OBSERVABLE PAYS BOTH E2 AND E4.
--
-- The older generic E2 interface asked for an encoding of EVERY stress tensor
-- into the cylinder algebra.  The marked reconstruction consumes only the one
-- selected Local-C stress.  Existing OS2 is already positive for every admitted
-- physical cylinder test family, so the selected mark needs only:
--
--   * one cylinder observable;
--   * positive-time support;
--   * gauge invariance.
--
-- Reflection of that observable inside the Gram form is owned by the EXISTING
-- cylinder algebra.  No separate all-stress reflection map is needed to prove
-- E2 positivity.
--
-- Round279/281 clustering is likewise quantified over arbitrary observables, so
-- the exact same selected cylinder observable feeds E4 directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 1ℝ; 0ℝ; _≤ℝ_)

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureContinuumOS2Exact as FiniteOS2
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as GramOS
import DASHI.Physics.YangMills.BalabanCMP116119NormalizedExpectationDerivativeRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceSpatialShellRound279Exact as R279
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

record SelectedLocalCStressCylinder
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₁ where
  field
    selectedObservable : Configuration → ℝ

    PositiveTimeSupported : (Configuration → ℝ) → Set
    GaugeInvariantObservable : (Configuration → ℝ) → Set

    selectedPositiveTime : PositiveTimeSupported selectedObservable
    selectedGaugeInvariant : GaugeInvariantObservable selectedObservable

    -- Same-object identity: this observable is the cylinder insertion of the
    -- selected Local-C stress.  The relation is kept abstract because Local-C's
    -- StressTensor carrier itself is not a function-on-configurations carrier.
    SelectedStressObservableMeaning :
      Top.StressTensor C → (Configuration → ℝ) → Set

    selectedObservableMeansLocalCStress :
      SelectedStressObservableMeaning
        (LocalC.stressTensor localC)
        selectedObservable

open SelectedLocalCStressCylinder public

selectedPositiveTimeCylinderTest :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (selected :
      SelectedLocalCStressCylinder
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
        localC) →
  Gram.PhysicalPositiveTimeCylinderTest (Configuration → ℝ) ℝ
selectedPositiveTimeCylinderTest selected =
  Gram.cylinderTest
    (selectedObservable selected)
    1ℝ
    (selectedPositiveTime selected)
    (selectedGaugeInvariant selected)

selectedSingletonFamily :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (selected :
      SelectedLocalCStressCylinder
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
        localC) →
  Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ
selectedSingletonFamily selected =
  Gram.finiteTestFamily
    (selectedPositiveTimeCylinderTest selected ∷ [])

selectedStressContinuumOS2 :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (selected :
      SelectedLocalCStressCylinder
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
        localC) →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations (OSSystem.observableAlgebra osInputs))
      (DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact.limitExpectation
        (OSSystem.family osInputs group))
      (selectedSingletonFamily selected)
selectedStressContinuumOS2
    {osInputs = osInputs} {group = group} selected =
  FiniteOS2.continuumReflectionPositive
    (OSSystem.finiteOS2Inputs osInputs group)
    (selectedSingletonFamily selected)

------------------------------------------------------------------------
-- E4 on the SAME selected observable.
------------------------------------------------------------------------

selectedStressGeometricClustering :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC Scalar SourceDirection algebra calculus published meaning round281}
    (selected :
      SelectedLocalCStressCylinder
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
        localC)
    (round281 :
      R281.LiteralTwoSourceNormalizedExpectationWeld
        {algebra = algebra} {calculus = calculus}
        {published = published} {meaning = meaning})
    scale volume other →
  R279.connectedCovarianceMagnitude
      (R281.asRound279SpatialShell round281)
      scale volume (selectedObservable selected) other
  ≤
  Shared.hessianAnalyticConstant
      (R279.shared (R281.asRound279SpatialShell round281))
  *
  (StepV.quarter
    * Geo.halfPower
        (R279.physicalDistance
          (R281.asRound279SpatialShell round281)
          (selectedObservable selected) other))
selectedStressGeometricClustering selected round281 scale volume other =
  R279.connectedCovarianceGeometricBound
    (R281.asRound279SpatialShell round281)
    scale volume (selectedObservable selected) other

selectedStressOnlySufficesForE2 : Bool
selectedStressOnlySufficesForE2 = true

selectedStressOnlySufficesForE4 : Bool
selectedStressOnlySufficesForE4 = true

allStressCylinderEncodingNoLongerParetoPremise : Bool
allStressCylinderEncodingNoLongerParetoPremise = false

remainingSharedPhysicalLeafIsOneSelectedObservableAndAdmissibility : Bool
remainingSharedPhysicalLeafIsOneSelectedObservableAndAdmissibility = true

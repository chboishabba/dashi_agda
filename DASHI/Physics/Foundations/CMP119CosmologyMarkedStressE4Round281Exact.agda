{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE4Round281Exact where

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.BalabanCMP116119NormalizedExpectationDerivativeRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceSpatialShellRound279Exact as R279
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

record LocalCStressRound281Selection
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core Observable Scalar SourceDirection : Set}
    {sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    {algebra : Cumulant.TwoSourceMomentAlgebra Observable Scalar}
    {calculus : Cumulant.NormalizedLogSourceCalculus algebra}
    {published : R281.CMP116119PublishedTwoSourceLocalization Scale Volume Root}
    {meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        osInputs reconstruction group)
    (round281 : R281.LiteralTwoSourceNormalizedExpectationWeld published meaning)
    : Set₁ where
  field
    stressObservableOf : StressTensor → Observable

open LocalCStressRound281Selection public

selectedStressObservable :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core Observable Scalar SourceDirection
      sequenceLimit limitLaws quotient division S osInputs reconstruction group
      algebra calculus published meaning localC round281} →
  LocalCStressRound281Selection
    {G} {X} {Configuration} {Position} {CurvaturePolynomial} {LocalOperator}
    {OPECoefficient} {StressTensor} {Hilbert} {Vector} {Hamiltonian} {Algebra}
    {Scale} {Volume} {Root} {ContinuumFamily} {Core} {Observable} {Scalar} {SourceDirection}
    {sequenceLimit} {limitLaws} {quotient} {division} {S}
    {osInputs} {reconstruction} {group}
    {algebra} {calculus} {published} {meaning}
    localC round281 →
  Observable
selectedStressObservable {localC = localC} selection =
  stressObservableOf selection (LocalC.stressTensor localC)

selectedStressSourceDirection :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core Observable Scalar SourceDirection
      sequenceLimit limitLaws quotient division S osInputs reconstruction group
      algebra calculus published meaning localC round281}
    (selection :
      LocalCStressRound281Selection
        {G} {X} {Configuration} {Position} {CurvaturePolynomial} {LocalOperator}
        {OPECoefficient} {StressTensor} {Hilbert} {Vector} {Hamiltonian} {Algebra}
        {Scale} {Volume} {Root} {ContinuumFamily} {Core} {Observable} {Scalar} {SourceDirection}
        {sequenceLimit} {limitLaws} {quotient} {division} {S}
        {osInputs} {reconstruction} {group}
        {algebra} {calculus} {published} {meaning}
        localC round281) →
  SourceDirection
selectedStressSourceDirection {meaning = meaning} selection =
  Cumulant.sourceDirectionOf meaning (selectedStressObservable selection)

selectedStressGeometricClustering :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core Observable Scalar SourceDirection
      sequenceLimit limitLaws quotient division S osInputs reconstruction group
      algebra calculus published meaning localC round281}
    (selection :
      LocalCStressRound281Selection
        {G} {X} {Configuration} {Position} {CurvaturePolynomial} {LocalOperator}
        {OPECoefficient} {StressTensor} {Hilbert} {Vector} {Hamiltonian} {Algebra}
        {Scale} {Volume} {Root} {ContinuumFamily} {Core} {Observable} {Scalar} {SourceDirection}
        {sequenceLimit} {limitLaws} {quotient} {division} {S}
        {osInputs} {reconstruction} {group}
        {algebra} {calculus} {published} {meaning}
        localC round281)
    scale volume other →
  R279.connectedCovarianceMagnitude
      (R281.asRound279SpatialShell round281)
      scale volume (selectedStressObservable selection) other
  ≤
  Shared.hessianAnalyticConstant
      (R279.shared (R281.asRound279SpatialShell round281))
  *
  (StepV.quarter
    * Geo.halfPower
        (R279.physicalDistance
          (R281.asRound279SpatialShell round281)
          (selectedStressObservable selection) other))
selectedStressGeometricClustering {round281 = round281}
    selection scale volume other =
  R279.connectedCovarianceGeometricBound
    (R281.asRound279SpatialShell round281)
    scale volume (selectedStressObservable selection) other

record SelectedMarkedE4
    {Scale Volume Root Observable : Set}
    (spatial : R279.CMP116TwoSourceSpatialShell Scale Volume Root Observable)
    (stressObservable : Observable)
    : Set₁ where
  constructor selected-marked-e4
  field
    stressClustersGeometrically :
      ∀ scale volume other →
      R279.connectedCovarianceMagnitude spatial
        scale volume stressObservable other
      ≤ Shared.hessianAnalyticConstant (R279.shared spatial)
          * (StepV.quarter
            * Geo.halfPower
                (R279.physicalDistance spatial stressObservable other))

selectedMarkedE4 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core Observable Scalar SourceDirection
      sequenceLimit limitLaws quotient division S osInputs reconstruction group
      algebra calculus published meaning localC round281}
    (selection :
      LocalCStressRound281Selection
        {G} {X} {Configuration} {Position} {CurvaturePolynomial} {LocalOperator}
        {OPECoefficient} {StressTensor} {Hilbert} {Vector} {Hamiltonian} {Algebra}
        {Scale} {Volume} {Root} {ContinuumFamily} {Core} {Observable} {Scalar} {SourceDirection}
        {sequenceLimit} {limitLaws} {quotient} {division} {S}
        {osInputs} {reconstruction} {group}
        {algebra} {calculus} {published} {meaning}
        localC round281) →
  SelectedMarkedE4
    (R281.asRound279SpatialShell round281)
    (selectedStressObservable selection)
selectedMarkedE4 selection =
  selected-marked-e4 (selectedStressGeometricClustering selection)

markedE4NoLongerNeedsIndependentDecayEstimate : Bool
markedE4NoLongerNeedsIndependentDecayEstimate = true

markedE4PhysicalLeafIsLocalCStressToLiteralJObservable : Bool
markedE4PhysicalLeafIsLocalCStressToLiteralJObservable = true

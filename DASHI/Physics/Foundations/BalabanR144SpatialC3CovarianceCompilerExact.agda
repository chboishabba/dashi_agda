{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.BalabanR144SpatialC3CovarianceCompilerExact where

------------------------------------------------------------------------
-- CANONICAL R144 B4 COVARIANCE -> SPATIAL C3 COVARIANCE COMPILER
--
-- The preferred cosmology route already declares the canonical R144 B4
-- readout covariance as A1.  Spatial C3 is not another source theorem: it is
-- the restriction of that same B4 covariance to the generator word
--
--   swap23 ; swap12
--
-- which fixes time and cycles x -> y -> z -> x.  This file proves that any
-- canonical A1 witness automatically supplies the corresponding two-step C3
-- readout covariance.  Therefore the C3 specialization adds no new terminal
-- physical leaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.CMP119CosmologyE1R144HypercubicReadoutMaxCutExact as R144E1
import DASHI.Physics.Foundations.CMP119CosmologyE1R144CanonicalB4ReadoutExact as A1

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact as R144Attach
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper

module _
    {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {source localization bc1Canonical}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
        {trajectory = trajectory} {split = split} {inputs = inputs}
        source localization bc1Canonical)
    {actionWeld :
      R132.UnifiedGeneratedActionDensity
        {trajectory = trajectory} {split = split} {inputs = inputs}
        (Present10.asPresentCutPhysicalSourceInputs presentData)}
    {laws :
      R143.PresentCutBC2FirstVariationLinearity
        (Present10.asPresentCutPhysicalSourceInputs presentData)}
    {composite : R144.CompositeStressFirstVariationInputs actionWeld laws}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {domain :
      Domain.CanonicalMetricSourceDomain
        Scale Volume (R144.stressActivity composite)}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    {selected : R119.CanonicalMetricSelectedStressWeld
      domain representation coordinate}
    (attachment :
      R144Attach.R144CanonicalMetricTangentAttachment
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = Present10.asPresentCutPhysicalSourceInputs presentData}
        {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        domain representation {coordinate = coordinate} selected)
  where

  Background : Set
  Background =
    Source.Background
      (Carrier.source
        (Present.bc1Carrier
          (Present10.asPresentCutPhysicalSourceInputs presentData)))

  swap23Component : K.SymmetricTensorComponent4 → K.SymmetricTensorComponent4
  swap23Component component =
    Signed.component
      (Signed.actSignedComponent
        (Axis.hypercubicSignedAxisAction Hyper.swap23) component)

  spatialC3SignedComponent :
    K.SymmetricTensorComponent4 → Signed.SignedSymmetricComponent
  spatialC3SignedComponent component =
    Signed.actSignedComponent
      (Axis.hypercubicSignedAxisAction Hyper.swap12)
      (swap23Component component)

  spatialC3Background :
    ∀ {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
      {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
      {quotient : Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
      {division : Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
      {family : Limit.FinitePhysicalNormalizedFamily
        Background limitLaws quotient division}
      (wholeLattice :
        Euclidean.CMP119WholeLatticeEuclideanCovariance
          Background Hyper.HypercubicGenerator family) →
    Background → Background
  spatialC3Background wholeLattice background =
    Euclidean.actConfiguration wholeLattice Hyper.swap12
      (Euclidean.actConfiguration wholeLattice Hyper.swap23 background)

  spatialC3ReadoutCovariant :
    ∀ {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
      {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
      {quotient : Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
      {division : Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
      {family : Limit.FinitePhysicalNormalizedFamily
        Background limitLaws quotient division}
      {wholeLattice :
        Euclidean.CMP119WholeLatticeEuclideanCovariance
          Background Hyper.HypercubicGenerator family} →
    A1.CanonicalB4R144ReadoutCovariance
      presentData attachment family wholeLattice →
    ∀ background component →
    R144E1.signedFiniteD1Readout presentData attachment
      (spatialC3Background wholeLattice background)
      (spatialC3SignedComponent component)
    ≡
    R144E1.finiteD1ReadoutAtComponent presentData attachment
      background component

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component00 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component00)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component00)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component01 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component01)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component01)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component02 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component03)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component02)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component03 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component02)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component03)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component11 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component11)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component11)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component12 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component13)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component12)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component13 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component12)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component13)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component22 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component33)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component22)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component23 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component23)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component23)

  spatialC3ReadoutCovariant {wholeLattice = wholeLattice}
      covariance background K.component33 =
    trans
      (A1.signedReadoutCovariant covariance Hyper.swap12
        (Euclidean.actConfiguration wholeLattice Hyper.swap23 background) K.component22)
      (A1.signedReadoutCovariant covariance Hyper.swap23 background K.component33)

spatialC3CovarianceCompilesFromCanonicalB4 : Bool
spatialC3CovarianceCompilesFromCanonicalB4 = true

independentSpatialC3PhysicalReceiptRequired : Bool
independentSpatialC3PhysicalReceiptRequired = false

spatialC3AddsAnotherTerminalA1Leaf : Bool
spatialC3AddsAnotherTerminalA1Leaf = false

spatialC3UsesExistingA1Twice : Bool
spatialC3UsesExistingA1Twice = true

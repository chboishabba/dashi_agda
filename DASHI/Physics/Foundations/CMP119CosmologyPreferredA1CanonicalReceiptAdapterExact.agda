{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredA1CanonicalReceiptAdapterExact where

------------------------------------------------------------------------
-- A1 ADAPTER ELIMINATION.
--
-- The canonical R144/B4 owner already states the exact rational finite-D1
-- covariance required by the preferred source receipt.  This module packages
-- that theorem into the typed A1 receipt without introducing a real-valued
-- surrogate, another action map, or another covariance assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsTypedReceiptsExact as Typed
import DASHI.Physics.Foundations.CMP119CosmologyE1R144CanonicalB4ReadoutExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyE1R144HypercubicReadoutMaxCutExact as R144E1
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10

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

  asExactPreferredA1Receipt :
    ∀ {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
      {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
      {quotient : Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
      {division : Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
      {family :
        Limit.FinitePhysicalNormalizedFamily
          Background limitLaws quotient division}
      {wholeLattice :
        Euclidean.CMP119WholeLatticeEuclideanCovariance
          Background Hyper.HypercubicGenerator family} →
    A1.CanonicalB4R144ReadoutCovariance
      presentData attachment family wholeLattice →
    Typed.A1R144SignedB4SourceReceipt
      Background
      (Euclidean.actConfiguration wholeLattice)
      (R144E1.finiteD1ReadoutAtComponent presentData attachment)
  asExactPreferredA1Receipt covariance = record
    { Typed.A1R144SignedB4SourceReceipt.signedReadoutCovariant =
        A1.signedReadoutCovariant covariance
    }

  a1CanonicalCovarianceToTypedReceiptIsCompilerOnly : Bool
  a1CanonicalCovarianceToTypedReceiptIsCompilerOnly = true

  a1AdapterKeepsLiteralRationalReadout : Bool
  a1AdapterKeepsLiteralRationalReadout = true

  a1AdapterAddsNoSecondActionMap : Bool
  a1AdapterAddsNoSecondActionMap = true

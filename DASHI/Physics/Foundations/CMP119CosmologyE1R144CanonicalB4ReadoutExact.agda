{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1R144CanonicalB4ReadoutExact where

------------------------------------------------------------------------
-- CANONICAL B4 SPECIALIZATION OF THE TERMINAL R144 E1 CUT.
--
-- `CMP119CosmologyE1R144HypercubicReadoutMaxCutExact` still permits an
-- auxiliary map
--
--   HypercubicGenerator -> EuclideanAction.
--
-- For the shortest source-facing route that freedom is unnecessary.  Take the
-- Euclidean-action carrier itself to be the repository's literal seven
-- hypercubic generators.  Then the generator attachment is definitionally the
-- identity, leaving exactly one physical theorem: covariance of the selected
-- R144 ten-slot readout under that concrete B4 action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.CMP119CosmologyE1R144HypercubicReadoutMaxCutExact as R144E1

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

  record CanonicalB4R144ReadoutCovariance
      {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
      {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
      {quotient : Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
      {division : Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
      (family :
        Limit.FinitePhysicalNormalizedFamily
          Background limitLaws quotient division)
      (wholeLattice :
        Euclidean.CMP119WholeLatticeEuclideanCovariance
          Background Hyper.HypercubicGenerator family)
      : Set₁ where
    field
      signedReadoutCovariant :
        ∀ generator background component →
        R144E1.signedFiniteD1Readout presentData attachment
          (Euclidean.actConfiguration wholeLattice generator background)
          (Signed.actSignedComponent
            (Axis.hypercubicSignedAxisAction generator) component)
        ≡
        R144E1.finiteD1ReadoutAtComponent presentData attachment
          background component

  open CanonicalB4R144ReadoutCovariance public

  asGenericR144HypercubicCovariance :
    ∀ {sequenceLimit limitLaws quotient division family wholeLattice} →
    CanonicalB4R144ReadoutCovariance
      {sequenceLimit = sequenceLimit}
      {limitLaws = limitLaws}
      {quotient = quotient}
      {division = division}
      family wholeLattice →
    R144E1.R144HypercubicSignedReadoutCovariance
      presentData attachment family wholeLattice
  asGenericR144HypercubicCovariance covariance = record
    { R144E1.R144HypercubicSignedReadoutCovariance.generatorToEuclideanAction =
        λ generator → generator
    ; R144E1.R144HypercubicSignedReadoutCovariance.signedReadoutCovariant =
        signedReadoutCovariant covariance
    }

  canonicalB4GeneratorAttachmentIsIdentity : Bool
  canonicalB4GeneratorAttachmentIsIdentity = true

  noIndependentGeneratorToEuclideanActionMap : Bool
  noIndependentGeneratorToEuclideanActionMap = true

  terminalCanonicalB4E1PhysicalLeafCount : Nat
  terminalCanonicalB4E1PhysicalLeafCount = 1

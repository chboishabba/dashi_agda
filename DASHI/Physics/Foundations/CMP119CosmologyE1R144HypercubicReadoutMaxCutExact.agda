{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1R144HypercubicReadoutMaxCutExact where

------------------------------------------------------------------------
-- TERMINAL E1 MAX-CUT: THE ACTUAL R144 TEN-SLOT READOUT IS A SIGNED B_4 TENSOR.
--
-- This is the consumer-level marked-E1 theorem.  It pins together:
--   * the literal R144 finite localized D1 readout;
--   * the SAME whole-lattice CMP119 Euclidean action used by OS1;
--   * the repository's seven concrete hypercubic generators; and
--   * the signed rank-two action on symmetric metric/stress slots.
--
-- Local CMP116 component covariance, finite reindexing and derivative
-- naturality are a preferred proof route to the single field below; they are
-- not separately charged terminal residuals.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; -_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119TenFiniteD1ComponentCompilerExact as TenD1
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis

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

axesOfComponent : K.SymmetricTensorComponent4 → Flat.Axis4 × Flat.Axis4
axesOfComponent K.component00 = Flat.timeAxis , Flat.timeAxis
axesOfComponent K.component01 = Flat.timeAxis , Flat.xAxis
axesOfComponent K.component02 = Flat.timeAxis , Flat.yAxis
axesOfComponent K.component03 = Flat.timeAxis , Flat.zAxis
axesOfComponent K.component11 = Flat.xAxis , Flat.xAxis
axesOfComponent K.component12 = Flat.xAxis , Flat.yAxis
axesOfComponent K.component13 = Flat.xAxis , Flat.zAxis
axesOfComponent K.component22 = Flat.yAxis , Flat.yAxis
axesOfComponent K.component23 = Flat.yAxis , Flat.zAxis
axesOfComponent K.component33 = Flat.zAxis , Flat.zAxis

applyRationalBasisSign : Signed.BasisSign → ℚ → ℚ
applyRationalBasisSign Signed.plus value = value
applyRationalBasisSign Signed.minus value = - value

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

  finiteD1ReadoutAtComponent :
    Background → K.SymmetricTensorComponent4 → ℚ
  finiteD1ReadoutAtComponent background component with axesOfComponent component
  ... | a , b =
    TenD1.finiteD1ReadoutAtAxes
      presentData attachment background a b

  signedFiniteD1Readout :
    Background → Signed.SignedSymmetricComponent → ℚ
  signedFiniteD1Readout background signed =
    applyRationalBasisSign (Signed.sign signed)
      (finiteD1ReadoutAtComponent background (Signed.component signed))

  record R144HypercubicSignedReadoutCovariance
      {EuclideanAction : Set}
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
          Background EuclideanAction family)
      : Set₁ where
    field
      generatorToEuclideanAction :
        Hyper.HypercubicGenerator → EuclideanAction

      -- The selected R144 stress readout transforms as the symmetric rank-two
      -- tensor attached to the SAME whole-lattice configuration action.
      signedReadoutCovariant :
        ∀ generator background component →
        signedFiniteD1Readout
          (Euclidean.actConfiguration wholeLattice
            (generatorToEuclideanAction generator) background)
          (Signed.actSignedComponent
            (Axis.hypercubicSignedAxisAction generator) component)
        ≡ finiteD1ReadoutAtComponent background component

  open R144HypercubicSignedReadoutCovariance public

  e1TerminalReadoutCovariance :
    ∀ {EuclideanAction sequenceLimit limitLaws quotient division family wholeLattice}
      (covariance :
        R144HypercubicSignedReadoutCovariance
          {EuclideanAction = EuclideanAction}
          {sequenceLimit = sequenceLimit}
          {limitLaws = limitLaws}
          {quotient = quotient}
          {division = division}
          family wholeLattice) →
    ∀ generator background component →
    signedFiniteD1Readout
      (Euclidean.actConfiguration wholeLattice
        (generatorToEuclideanAction covariance generator) background)
      (Signed.actSignedComponent
        (Axis.hypercubicSignedAxisAction generator) component)
    ≡ finiteD1ReadoutAtComponent background component
  e1TerminalReadoutCovariance = signedReadoutCovariant

  localCMP116NaturalityIsProducerStrategyNotSecondTerminalLeaf : Bool
  localCMP116NaturalityIsProducerStrategyNotSecondTerminalLeaf = true

  r133TransportEquivarianceIsTerminalE1Leaf : Bool
  r133TransportEquivarianceIsTerminalE1Leaf = false

  terminalE1PhysicalLeafCount : Nat
  terminalE1PhysicalLeafCount = 1

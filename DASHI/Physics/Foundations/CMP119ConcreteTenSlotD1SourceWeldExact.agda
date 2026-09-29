{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ConcreteTenSlotD1SourceWeldExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (proj₁; proj₂)\nopen import Data.Rational.Base using (-[1+_])
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ConcreteTenSlotCrossNumeratorCandidateExact as Candidate
import DASHI.Physics.Foundations.CMP119TenFiniteD1ComponentCompilerExact as D1
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutCarrierCompilerExact as Present10
import DASHI.Physics.Foundations.CMP119SymmetricPresentCutMetricBasisCompilerExact as PresentBasis
import DASHI.Physics.Foundations.CMP119SymmetricMetricBasisRealizationExact as MetricBasis
import DASHI.Physics.Foundations.CMP119MetricBasisStressComponentCompilerExact as Basis
import DASHI.Physics.Foundations.GRQFTNegativeActiveStressRepulsionRouteExact as Negative
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as SourceFlow
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as Local
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

------------------------------------------------------------------------
-- ONE SAME-OBJECT WELD PAYS ALL TEN FINITE-D1 NUMBERS
--
-- Candidate gives a concrete normalized cross numerator on the literal
-- beta-driven Density carrier.  The only remaining source theorem for this
-- candidate route is that the post-sum R144/R119 finite-D1 readout is that SAME
-- normalized source derivative on every one of the ten symmetric tangents.
------------------------------------------------------------------------

module _
    {History Cell : Set} {cutoff : Nat}
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {source : SourceFlow.FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs}
    {localization : Local.CMP119RegularELocalizationCarrier source}
    {bc1Canonical : Present10.SymmetricFunctionalRegularEBC1Inputs
      source localization}
    (presentData :
      Present10.SymmetricFunctionalRegularEPresentCutInputs History Cell cutoff
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
    {selected :
      R119.CanonicalMetricSelectedStressWeld
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
    (background :
      Source.Background
        (Carrier.source
          (Present.bc1Carrier
            (Present10.asPresentCutPhysicalSourceInputs presentData))))
    (scale : Nat)
  where

  record ConcreteTenSlotD1SourceWeld : Set₁ where
    field
      finiteD1ReadoutIsConcreteCrossNumerator :
        ∀ component →
        D1.finiteD1ReadoutAtAxes
          presentData attachment background
          (proj₁ (Sym.symmetricComponentAxes component))
          (proj₂ (Sym.symmetricComponentAxes component))
        ≡ Candidate.crossNumeratorAt inputs scale component

  open ConcreteTenSlotD1SourceWeld public

  normalizedTenFiniteD1Values :
    ConcreteTenSlotD1SourceWeld →
    D1.NormalizedTenFiniteD1Values presentData attachment background
  normalizedTenFiniteD1Values weld = record
    { D1.NormalizedTenFiniteD1Values.d100 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component00)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component00)
    ; D1.NormalizedTenFiniteD1Values.d101 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component01)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component01)
    ; D1.NormalizedTenFiniteD1Values.d102 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component02)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component02)
    ; D1.NormalizedTenFiniteD1Values.d103 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component03)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component03)
    ; D1.NormalizedTenFiniteD1Values.d111 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component11)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component11)
    ; D1.NormalizedTenFiniteD1Values.d112 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component12)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component12)
    ; D1.NormalizedTenFiniteD1Values.d113 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component13)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component13)
    ; D1.NormalizedTenFiniteD1Values.d122 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component22)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component22)
    ; D1.NormalizedTenFiniteD1Values.d123 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component23)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component23)
    ; D1.NormalizedTenFiniteD1Values.d133 =
        trans
          (finiteD1ReadoutIsConcreteCrossNumerator weld K.component33)
          (Candidate.crossNumeratorComputesTarget inputs scale K.component33)
    }

  normalizedMetricTenComponentInstance :
    ConcreteTenSlotD1SourceWeld →
    let realization =
          PresentBasis.compilePresentCutTenSlotMetricBasis
            presentData attachment background
        basis = MetricBasis.compileSymmetricBasis16 realization
        readout = D1.canonicalR119Readout selected
        evaluator = Basis.cmp119MetricBasisEvaluator basis readout
    in
    Sym.NormalizedSymmetricTenComponentInstance
      evaluator
      (StressRep.stressTensor representation)
  normalizedMetricTenComponentInstance weld =
    let
      values = normalizedTenFiniteD1Values weld
      realization =
        PresentBasis.compilePresentCutTenSlotMetricBasis
          presentData attachment background
      readout = D1.canonicalR119Readout selected
    in record
      { Sym.NormalizedSymmetricTenComponentInstance.symmetry =
          Sym.metricBasisEvaluatorIsComponentSymmetric
            realization readout (StressRep.stressTensor representation)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft00 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.timeAxis Flat.timeAxis)
            (D1.d100 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft01 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.timeAxis Flat.xAxis)
            (D1.d101 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft02 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.timeAxis Flat.yAxis)
            (D1.d102 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft03 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.timeAxis Flat.zAxis)
            (D1.d103 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft11 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.xAxis Flat.xAxis)
            (D1.d111 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft12 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.xAxis Flat.yAxis)
            (D1.d112 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft13 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.xAxis Flat.zAxis)
            (D1.d113 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft22 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.yAxis Flat.yAxis)
            (D1.d122 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft23 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.yAxis Flat.zAxis)
            (D1.d123 values)
      ; Sym.NormalizedSymmetricTenComponentInstance.qft33 =
          trans
            (D1.metricComponentIsFiniteD1Readout
              presentData attachment background Flat.zAxis Flat.zAxis)
            (D1.d133 values)
      }

  activeStressIsNegativeTwo :
    (weld : ConcreteTenSlotD1SourceWeld) →
    let realization =
          PresentBasis.compilePresentCutTenSlotMetricBasis
            presentData attachment background
        basis = MetricBasis.compileSymmetricBasis16 realization
        readout = D1.canonicalR119Readout selected
        evaluator = Basis.cmp119MetricBasisEvaluator basis readout
    in
    Negative.cmp119ActiveStressSum
      evaluator
      (StressRep.stressTensor representation)
    ≡ -[1+ suc zero ]
  activeStressIsNegativeTwo weld =
    Negative.tenComponentsCompileToNegativeActiveStress
      (normalizedMetricTenComponentInstance weld)

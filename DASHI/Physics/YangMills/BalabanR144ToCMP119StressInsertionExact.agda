{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR144ToCMP119StressInsertionExact where

------------------------------------------------------------------------
-- C / R144 FINITE LOCALIZED D1 -> EXACT SELECTED CMP119 STRESS INSERTION
--
-- R144 already proves that the global stress first variation is the whole
-- localized D1 sum. R119/R118 already prove that the canonical metric first
-- variation is the exact selected CMP119 normalized insertion. The only
-- remaining bridge is the literal convention/same-coordinate identification
-- between those two finite first-variation readouts.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record R144ToSelectedCMP119StressInsertion
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    {laws : R143.PresentCutBC2FirstVariationLinearity present}
    (composite : R144.CompositeStressFirstVariationInputs actionWeld laws)
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
    : Set₁ where
  field
    finiteD1ToRational : ℝ → ℚ

    toMetricBackground :
      Finite.Configuration (Carrier.finiteAction (Present.bc1Carrier present)) →
      Chain.Background activity

    toMetricPerturbation :
      Finite.Tangent (Carrier.finiteAction (Present.bc1Carrier present)) →
      Domain.MetricPerturbation domain

    selectedMetricPerturbationAdmissible :
      ∀ background tangent →
      Domain.AdmissibleMetricPerturbation domain
        (toMetricPerturbation tangent)

    -- Exact finite same-coordinate/convention weld. No continuum statement is
    -- hidden here.
    localizedD1IsCanonicalMetricReadout :
      ∀ background tangent →
      finiteD1ToRational
        (D1.finiteLocalizedFirstVariation
          (Carrier.finiteAction (Present.bc1Carrier present))
          (R143.asFirstVariationLinearity laws)
          background tangent)
      ≡
      R118.readoutToRational
        (R119.asRound118CanonicalMetricWeld selected)
        (StressRep.firstVariationReadout representation
          (First.substitutedFirstVariation activity
            (toMetricBackground background)
            (Domain.metricPerturbationToBackgroundTangent
              domain
              (toMetricBackground background)
              (toMetricPerturbation tangent))))

open R144ToSelectedCMP119StressInsertion public

r144LocalizedD1IsSelectedCMP119Insertion :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite C S Y group Scale Volume activity domain representation
      coordinate selected}
    (weld :
      R144ToSelectedCMP119StressInsertion
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume} {activity = activity}
        {domain = domain} {representation = representation}
        {coordinate = coordinate} selected) →
  ∀ background tangent →
  let
    metricBackground = toMetricBackground weld background
    perturbation = toMetricPerturbation weld tangent
    insertion =
      R118.normalizedInsertion
        (R119.asRound118CanonicalMetricWeld selected)
        metricBackground perturbation
  in
  finiteD1ToRational weld
    (D1.finiteLocalizedFirstVariation
      (Carrier.finiteAction (Present.bc1Carrier present))
      (R143.asFirstVariationLinearity laws)
      background tangent)
  ≡ R116.cmp119StressInsertionNumerator insertion
r144LocalizedD1IsSelectedCMP119Insertion
    {selected = selected} weld background tangent =
  trans
    (localizedD1IsCanonicalMetricReadout weld background tangent)
    (R119.canonicalMetricVariationIsExactSelectedCMP119StressInsertion
      selected
      (toMetricBackground weld background)
      (toMetricPerturbation weld tangent)
      (selectedMetricPerturbationAdmissible weld background tangent))

r144ToSelectedCMP119StressCompilerLevel : ProofLevel
r144ToSelectedCMP119StressCompilerLevel = machineChecked

-- Genuine finite stress seam after reuse of R144 and R119:
-- identify the localized BC1/BC2 D1 scalar with the canonical metric-variation
-- readout on the same literal stress coordinate, including only the explicit
-- real-to-rational convention map.
literalR144CanonicalMetricSameCoordinateLevel : ProofLevel
literalR144CanonicalMetricSameCoordinateLevel = conditional

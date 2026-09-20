{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentAttachmentExact where

------------------------------------------------------------------------
-- C / R144 STRESS TANGENT -> CANONICAL METRIC READOUT
--
-- The older R144->CMP119 adapter stored as a field the scalar equality
--
--   finite localized D1 readout = canonical metric first-variation readout.
--
-- That equality is stronger than the physical seam.  If the canonical metric
-- source domain is instantiated on the SAME substituted stress activity as
-- Round144, and the selected metric perturbation maps to the SAME stress
-- background tangent, then the readout equality follows by congruence from
-- Round144's theorem that the substituted stress first variation is the whole
-- finite localized D1 sum.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanR144ToCMP119StressInsertionExact as Old
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record R144CanonicalMetricTangentAttachment
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
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
    (domain :
      Domain.CanonicalMetricSourceDomain
        Scale Volume (R144.stressActivity composite))
    (representation : StressRep.CanonicalMetricStressRepresentation domain)
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
    : Set₁ where
  field
    toMetricPerturbation :
      Finite.Tangent
        (Carrier.finiteAction (Present.bc1Carrier present)) →
      Domain.MetricPerturbation domain

    selectedMetricPerturbationAdmissible :
      ∀ background tangent →
      Domain.AdmissibleMetricPerturbation domain
        (toMetricPerturbation tangent)

    metricPerturbationRealizesR144StressTangent :
      ∀ background tangent →
      Domain.metricPerturbationToBackgroundTangent
        domain
        (R144.globalBackgroundToStressBackground composite background)
        (toMetricPerturbation tangent)
      ≡
      R144.globalTangentToStressTangent composite tangent

open R144CanonicalMetricTangentAttachment public

finiteD1ToCanonicalMetricRational :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite C S Y group Scale Volume domain representation coordinate
      selected} →
  R144CanonicalMetricTangentAttachment
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {laws = laws}
    composite
    {C = C} {S = S} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume}
    domain representation {coordinate = coordinate} selected →
  DASHI.Foundations.RealAnalysisAxioms.ℝ → ℚ
finiteD1ToCanonicalMetricRational {representation = representation}
    {selected = selected} attachment value =
  R118.readoutToRational
    (R119.asRound118CanonicalMetricWeld selected)
    (StressRep.firstVariationReadout representation value)

localizedD1IsCanonicalMetricReadout :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite C S Y group Scale Volume domain representation coordinate
      selected}
    (attachment :
      R144CanonicalMetricTangentAttachment
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        domain representation {coordinate = coordinate} selected) →
  ∀ background tangent →
  finiteD1ToCanonicalMetricRational attachment
    (D1.finiteLocalizedFirstVariation
      (Carrier.finiteAction (Present.bc1Carrier present))
      (R143.asFirstVariationLinearity laws)
      background tangent)
  ≡
  R118.readoutToRational
    (R119.asRound118CanonicalMetricWeld selected)
    (StressRep.firstVariationReadout representation
      (First.substitutedFirstVariation
        (R144.stressActivity composite)
        (R144.globalBackgroundToStressBackground composite background)
        (Domain.metricPerturbationToBackgroundTangent
          domain
          (R144.globalBackgroundToStressBackground composite background)
          (toMetricPerturbation attachment tangent))))
localizedD1IsCanonicalMetricReadout
    {present = present} {laws = laws}
    {composite = composite} {representation = representation}
    {selected = selected} attachment background tangent =
  let
    readout =
      λ value →
        R118.readoutToRational
          (R119.asRound118CanonicalMetricWeld selected)
          (StressRep.firstVariationReadout representation value)

    finiteToStress :
      readout
        (D1.finiteLocalizedFirstVariation
          (Carrier.finiteAction (Present.bc1Carrier present))
          (R143.asFirstVariationLinearity laws)
          background tangent)
      ≡
      readout
        (First.substitutedFirstVariation
          (R144.stressActivity composite)
          (R144.globalBackgroundToStressBackground composite background)
          (R144.globalTangentToStressTangent composite tangent))
    finiteToStress =
      cong readout
        (sym
          (R144.stressFirstVariationIsFiniteLocalizedSum
            composite background tangent))

    tangentReadout :
      readout
        (First.substitutedFirstVariation
          (R144.stressActivity composite)
          (R144.globalBackgroundToStressBackground composite background)
          (R144.globalTangentToStressTangent composite tangent))
      ≡
      readout
        (First.substitutedFirstVariation
          (R144.stressActivity composite)
          (R144.globalBackgroundToStressBackground composite background)
          (Domain.metricPerturbationToBackgroundTangent
            domain
            (R144.globalBackgroundToStressBackground composite background)
            (toMetricPerturbation attachment tangent)))
    tangentReadout =
      cong readout
        (cong
          (First.substitutedFirstVariation
            (R144.stressActivity composite)
            (R144.globalBackgroundToStressBackground composite background))
          (sym
            (metricPerturbationRealizesR144StressTangent
              attachment background tangent)))
  in
  trans finiteToStress tangentReadout

asOldR144ToSelectedCMP119StressInsertion :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite C S Y group Scale Volume domain representation coordinate
      selected}
    (attachment :
      R144CanonicalMetricTangentAttachment
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld} {laws = laws}
        composite
        {C = C} {S = S} {Y = Y} {group = group}
        {Scale = Scale} {Volume = Volume}
        domain representation {coordinate = coordinate} selected) →
  Old.R144ToSelectedCMP119StressInsertion
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {laws = laws}
    composite
    {C = C} {S = S} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume}
    {activity = R144.stressActivity composite}
    {domain = domain} {representation = representation}
    {coordinate = coordinate} selected
asOldR144ToSelectedCMP119StressInsertion
    {composite = composite} attachment = record
  { Old.R144ToSelectedCMP119StressInsertion.finiteD1ToRational =
      finiteD1ToCanonicalMetricRational attachment
  ; Old.R144ToSelectedCMP119StressInsertion.toMetricBackground =
      R144.globalBackgroundToStressBackground composite
  ; Old.R144ToSelectedCMP119StressInsertion.toMetricPerturbation =
      toMetricPerturbation attachment
  ; Old.R144ToSelectedCMP119StressInsertion.selectedMetricPerturbationAdmissible =
      selectedMetricPerturbationAdmissible attachment
  ; Old.R144ToSelectedCMP119StressInsertion.localizedD1IsCanonicalMetricReadout =
      localizedD1IsCanonicalMetricReadout attachment
  }

r144CanonicalMetricTangentAttachmentCompilerLevel : ProofLevel
r144CanonicalMetricTangentAttachmentCompilerLevel = machineChecked

-- The physical R144/R119 seam is now only:
--   metric perturbation -> the SAME R144 stress tangent,
-- plus admissibility in the canonical metric source domain.
-- The scalar readout equality itself is no longer a research leaf.
literalMetricPerturbationR144TangentAttachmentLevel : ProofLevel
literalMetricPerturbationR144TangentAttachmentLevel = conditional

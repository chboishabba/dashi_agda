{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR144CanonicalMetricTangentRound428Exact where

------------------------------------------------------------------------
-- C / ROUND428: METRIC TANGENT ATTACHMENT -> OLD R144 SCALAR WELD
--
-- R144 already proves
--
--   substituted stress first variation = whole localized D1 sum.
--
-- Therefore the old R144->CMP119 owner must not separately assume equality of
-- the localized-D1 scalar with the canonical metric readout.  It follows from:
--
--   (1) the selected metric perturbation realizes the R144 stress tangent;
--   (2) both lanes use the same explicit real->rational/readout convention.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanR144ToCMP119StressInsertionExact as Old
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
    {domain :
      Domain.CanonicalMetricSourceDomain
        Scale Volume (R144.stressActivity composite)}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {coordinate : R114.LiteralStressCoordinate Y group}
    (selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate)
    : Set₁ where
  field
    finiteD1ToRational : ℝ → ℚ

    -- Explicit convention equality only; no physics hidden here.
    finiteD1ToRationalIsMetricReadout :
      ∀ value →
      finiteD1ToRational value
      ≡
      R119.readoutToRational selected
        (StressRep.firstVariationReadout representation value)

    toMetricPerturbation :
      Source.Tangent (Carrier.source (Present.bc1Carrier present)) →
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

localizedD1IsCanonicalMetricReadoutFromTangent :
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
        {domain = domain} {representation = representation}
        {coordinate = coordinate} selected) →
  ∀ background tangent →
  finiteD1ToRational attachment
    (D1.finiteLocalizedFirstVariation
      (Carrier.finiteAction (Present.bc1Carrier present))
      (R143.asFirstVariationLinearity laws)
      background tangent)
  ≡
  R119.readoutToRational selected
    (StressRep.firstVariationReadout representation
      (First.substitutedFirstVariation
        (R144.stressActivity composite)
        (R144.globalBackgroundToStressBackground composite background)
        (Domain.metricPerturbationToBackgroundTangent
          domain
          (R144.globalBackgroundToStressBackground composite background)
          (toMetricPerturbation attachment tangent))))
localizedD1IsCanonicalMetricReadoutFromTangent
    {composite = composite} {selected = selected}
    attachment background tangent =
  trans
    (cong (finiteD1ToRational attachment)
      (sym
        (R144.stressFirstVariationIsFiniteLocalizedSum
          composite background tangent)))
    (trans
      (finiteD1ToRationalIsMetricReadout attachment
        (First.substitutedFirstVariation
          (R144.stressActivity composite)
          (R144.globalBackgroundToStressBackground composite background)
          (R144.globalTangentToStressTangent composite tangent)))
      (cong
        (R119.readoutToRational selected ∘
          StressRep.firstVariationReadout _ ∘
          First.substitutedFirstVariation
            (R144.stressActivity composite)
            (R144.globalBackgroundToStressBackground composite background))
        (sym
          (metricPerturbationRealizesR144StressTangent
            attachment background tangent))))
  where
  infixr 9 _∘_
  _∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)

asOldR144Weld :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite C S Y group Scale Volume domain representation coordinate}
    {selected :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate} →
  R144CanonicalMetricTangentAttachment
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {laws = laws}
    composite
    {C = C} {S = S} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume}
    {domain = domain} {representation = representation}
    {coordinate = coordinate} selected →
  Old.R144ToSelectedCMP119StressInsertion composite selected
asOldR144Weld {composite = composite} {selected = selected} attachment = record
  { Old.R144ToSelectedCMP119StressInsertion.finiteD1ToRational =
      finiteD1ToRational attachment
  ; Old.R144ToSelectedCMP119StressInsertion.toMetricBackground =
      R144.globalBackgroundToStressBackground composite
  ; Old.R144ToSelectedCMP119StressInsertion.toMetricPerturbation =
      toMetricPerturbation attachment
  ; Old.R144ToSelectedCMP119StressInsertion.selectedMetricPerturbationAdmissible =
      selectedMetricPerturbationAdmissible attachment
  ; Old.R144ToSelectedCMP119StressInsertion.localizedD1IsCanonicalMetricReadout =
      localizedD1IsCanonicalMetricReadoutFromTangent attachment
  }

round428MetricTangentToR144CompilerLevel : ProofLevel
round428MetricTangentToR144CompilerLevel = machineChecked

-- C4 is narrowed to the physical tangent realization plus the explicit scalar
-- convention.  The whole localized-D1/readout equality is compiler-owned.
literalRound428MetricTangentAttachmentLevel : ProofLevel
literalRound428MetricTangentAttachmentLevel = conditional

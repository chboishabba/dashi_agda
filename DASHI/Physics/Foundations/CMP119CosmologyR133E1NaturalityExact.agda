{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR133E1NaturalityExact where

------------------------------------------------------------------------
-- R133 SAME-ACTION FIRST VARIATION -> MARKED E1 NATURALITY.
--
-- R133 already proves that the stress-producing substituted CMP116 first
-- variation is the SAME BC2/global first variation after the declared
-- background/tangent transports.
--
-- Therefore marked E1 does not need a second stress covariance theorem.
-- It is enough that:
--
--   (1) the BC2/global first variation is Euclidean-action covariant;
--   (2) the R133 background transport commutes with that action;
--   (3) the R133 tangent transport commutes with that action.
--
-- Then the substituted stress first variation is equivariant automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE1DifferentiatedCovarianceExact as E1

record R133EuclideanActionNaturality
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    (firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld)
    : Set₁ where
  field
    EuclideanAction : Set

    actGlobalBackground :
      EuclideanAction →
      Source.Background (Carrier.source (Present.bc1Carrier present)) →
      Source.Background (Carrier.source (Present.bc1Carrier present))

    actGlobalTangent :
      EuclideanAction →
      Source.Tangent (Carrier.source (Present.bc1Carrier present)) →
      Source.Tangent (Carrier.source (Present.bc1Carrier present))

    actStressBackground :
      EuclideanAction →
      Chain.Background (R133.stressActivity firstWeld) →
      Chain.Background (R133.stressActivity firstWeld)

    actStressTangent :
      EuclideanAction →
      Chain.BackgroundTangent (R133.stressActivity firstWeld) →
      Chain.BackgroundTangent (R133.stressActivity firstWeld)

    backgroundTransportEquivariant :
      ∀ action background →
      R133.globalBackgroundToStressBackground firstWeld
        (actGlobalBackground action background)
      ≡
      actStressBackground action
        (R133.globalBackgroundToStressBackground firstWeld background)

    tangentTransportEquivariant :
      ∀ action tangent →
      R133.globalTangentToStressTangent firstWeld
        (actGlobalTangent action tangent)
      ≡
      actStressTangent action
        (R133.globalTangentToStressTangent firstWeld tangent)

    effectivePotentialCovariant :
      ∀ action background →
      Carrier.effectivePotential (Present.bc1Carrier present)
        (actGlobalBackground action background)
      ≡
      Carrier.effectivePotential (Present.bc1Carrier present)
        background

    bc2FirstVariationCovariant :
      ∀ action background tangent →
      BC2.firstVariation (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
        (actGlobalBackground action background)
        (actGlobalTangent action tangent)
      ≡
      BC2.firstVariation (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
        background tangent

open R133EuclideanActionNaturality public

r133StressFirstVariationEquivariant :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld}
    (naturality :
      R133EuclideanActionNaturality
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld}
        firstWeld)
    action background tangent →
  First.substitutedFirstVariation (R133.stressActivity firstWeld)
    (actStressBackground naturality action
      (R133.globalBackgroundToStressBackground firstWeld background))
    (actStressTangent naturality action
      (R133.globalTangentToStressTangent firstWeld tangent))
  ≡
  First.substitutedFirstVariation (R133.stressActivity firstWeld)
    (R133.globalBackgroundToStressBackground firstWeld background)
    (R133.globalTangentToStressTangent firstWeld tangent)
r133StressFirstVariationEquivariant
    {present = present} {firstWeld = firstWeld}
    naturality action background tangent =
  trans
    (cong₂
      (First.substitutedFirstVariation (R133.stressActivity firstWeld))
      (sym (backgroundTransportEquivariant naturality action background))
      (sym (tangentTransportEquivariant naturality action tangent)))
    (trans
      (sym
        (R133.sameActionFirstVariation firstWeld
          (actGlobalBackground naturality action background)
          (actGlobalTangent naturality action tangent)))
      (trans
        (bc2FirstVariationCovariant naturality action background tangent)
        (R133.sameActionFirstVariation firstWeld background tangent)))

e1NoLongerNeedsIndependentStressCovarianceLaw : Bool
e1NoLongerNeedsIndependentStressCovarianceLaw = true

e1ResidualIsBC2CovariancePlusTransportEquivariance : Bool
e1ResidualIsBC2CovariancePlusTransportEquivariance = true


asDifferentiatedEuclideanCovariance :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld}
    (naturality :
      R133EuclideanActionNaturality
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld}
        firstWeld) →
  E1.DifferentiatedEuclideanCovariance
    (EuclideanAction naturality)
    (Source.Background (Carrier.source (Present.bc1Carrier present)))
    (Source.Tangent (Carrier.source (Present.bc1Carrier present)))
    ℝ
asDifferentiatedEuclideanCovariance
    {present = present} naturality = record
  { E1.DifferentiatedEuclideanCovariance.actBase =
      actGlobalBackground naturality
  ; E1.DifferentiatedEuclideanCovariance.actStress =
      actGlobalTangent naturality
  ; E1.DifferentiatedEuclideanCovariance.baseExpectation =
      Carrier.effectivePotential (Present.bc1Carrier present)
  ; E1.DifferentiatedEuclideanCovariance.markedDerivative =
      BC2.firstVariation (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
  ; E1.DifferentiatedEuclideanCovariance.baseCovariant =
      effectivePotentialCovariant naturality
  ; E1.DifferentiatedEuclideanCovariance.derivativeEquivariant =
      bc2FirstVariationCovariant naturality
  }

r133InstantiatesGenericMarkedE1Carrier : Bool
r133InstantiatesGenericMarkedE1Carrier = true

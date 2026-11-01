{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1WholeLatticeLocalizedMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyE1LocalizedD1CovarianceExact as LocalE1
import DASHI.Physics.Foundations.CMP119CosmologyE1R143LocalizedCompilerExact as R143E1
import DASHI.Physics.Foundations.CMP119CosmologyE1FiniteEuclideanAttachmentExact as Attach
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity

record WholeLatticeLocalizedE1MaxCut
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    (firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld)
    (laws : R143.PresentCutBC2FirstVariationLinearity present)
    {EuclideanAction : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        (Source.Background (Carrier.source (Present.bc1Carrier present)))
        limitLaws quotient division)
    (euclidean :
      Euclidean.CMP119WholeLatticeEuclideanCovariance
        (Source.Background (Carrier.source (Present.bc1Carrier present)))
        EuclideanAction family)
    : Set₁ where
  field
    localized :
      R143E1.R143LocalizedEuclideanCovariance
        present laws EuclideanAction

    localizedBackgroundActionIsWholeLattice :
      ∀ action background →
      LocalE1.actConfiguration
        (R143E1.localized localized) action background
      ≡
      Euclidean.actConfiguration euclidean action background

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
        (Euclidean.actConfiguration euclidean action background)
      ≡
      actStressBackground action
        (R133.globalBackgroundToStressBackground firstWeld background)

    tangentTransportEquivariant :
      ∀ action tangent →
      R133.globalTangentToStressTangent firstWeld
        (LocalE1.actTangent
          (R143E1.localized localized) action tangent)
      ≡
      actStressTangent action
        (R133.globalTangentToStressTangent firstWeld tangent)

open WholeLatticeLocalizedE1MaxCut public

wholeLatticePotentialCovariant :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld
      firstWeld laws EuclideanAction sequenceLimit limitLaws quotient division
      family euclidean}
    (cut :
      WholeLatticeLocalizedE1MaxCut
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld}
        firstWeld laws
        {EuclideanAction = EuclideanAction}
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family euclidean)
    action background →
  Carrier.effectivePotential (Present.bc1Carrier present)
    (Euclidean.actConfiguration euclidean action background)
  ≡
  Carrier.effectivePotential (Present.bc1Carrier present)
    background
wholeLatticePotentialCovariant
    {present = present} cut action background =
  subst
    (λ moved →
      Carrier.effectivePotential (Present.bc1Carrier present) moved
      ≡
      Carrier.effectivePotential (Present.bc1Carrier present) background)
    (localizedBackgroundActionIsWholeLattice cut action background)
    (LocalE1.cmp109EffectivePotentialCovariant
      (R143E1.localized (localized cut)) action background)

wholeLatticeBC2FirstVariationCovariant :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld
      firstWeld laws EuclideanAction sequenceLimit limitLaws quotient division
      family euclidean}
    (cut :
      WholeLatticeLocalizedE1MaxCut
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {History = History} {Cell = Cell} {cutoff = cutoff}
        {present = present} {actionWeld = actionWeld}
        firstWeld laws
        {EuclideanAction = EuclideanAction}
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family euclidean)
    action background tangent →
  BC2.firstVariation (Present.bc2 present)
    (Carrier.effectivePotential (Present.bc1Carrier present))
    (Euclidean.actConfiguration euclidean action background)
    (LocalE1.actTangent
      (R143E1.localized (localized cut)) action tangent)
  ≡
  BC2.firstVariation (Present.bc2 present)
    (Carrier.effectivePotential (Present.bc1Carrier present))
    background tangent
wholeLatticeBC2FirstVariationCovariant
    {present = present} cut action background tangent =
  subst
    (λ moved →
      BC2.firstVariation (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
        moved
        (LocalE1.actTangent
          (R143E1.localized (localized cut)) action tangent)
      ≡
      BC2.firstVariation (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
        background tangent)
    (localizedBackgroundActionIsWholeLattice cut action background)
    (R143E1.bc2FirstVariationCovariantFromLocalizedD1
      (localized cut) action background tangent)

asFiniteEuclideanBC1Attachment :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld
      firstWeld laws EuclideanAction sequenceLimit limitLaws quotient division
      family euclidean} →
  WholeLatticeLocalizedE1MaxCut
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld}
    firstWeld laws
    {EuclideanAction = EuclideanAction}
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family euclidean →
  Attach.FiniteEuclideanBC1Attachment
    firstWeld family euclidean
asFiniteEuclideanBC1Attachment cut = record
  { Attach.FiniteEuclideanBC1Attachment.actGlobalTangent =
      LocalE1.actTangent
        (R143E1.localized (localized cut))
  ; Attach.FiniteEuclideanBC1Attachment.actStressBackground =
      actStressBackground cut
  ; Attach.FiniteEuclideanBC1Attachment.actStressTangent =
      actStressTangent cut
  ; Attach.FiniteEuclideanBC1Attachment.backgroundTransportEquivariant =
      backgroundTransportEquivariant cut
  ; Attach.FiniteEuclideanBC1Attachment.tangentTransportEquivariant =
      tangentTransportEquivariant cut
  ; Attach.FiniteEuclideanBC1Attachment.effectivePotentialCovariant =
      wholeLatticePotentialCovariant cut
  ; Attach.FiniteEuclideanBC1Attachment.bc2FirstVariationCovariant =
      wholeLatticeBC2FirstVariationCovariant cut
  }

e1PotentialAndGlobalDerivativeCovarianceNowCompilerOutput : Bool
e1PotentialAndGlobalDerivativeCovarianceNowCompilerOutput = true

e1LiveLeavesAreLocalGeometryAndR133Transport : Bool
e1LiveLeavesAreLocalGeometryAndR133Transport = true

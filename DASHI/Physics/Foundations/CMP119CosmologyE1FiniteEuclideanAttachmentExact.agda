{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1FiniteEuclideanAttachmentExact where

------------------------------------------------------------------------
-- ATTACH THE ACTUAL CMP119 WHOLE-LATTICE EUCLIDEAN ACTION TO THE BC1/R133
-- BACKGROUND/TANGENT CARRIER.
--
-- The finite OS1 source already owns:
--
--   actConfiguration : EuclideanAction -> Configuration -> Configuration.
--
-- For E1 we must use THAT SAME action on the BC1 background, not invent a
-- second Euclidean action.  This owner therefore fixes the finite-family
-- Configuration carrier to the exact BC1 Background carrier.
--
-- The only additional geometry is the tangent action and the derivative
-- naturality/covariance of the selected effective potential under this same
-- configuration action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyR133E1NaturalityExact as E1R133
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133

record FiniteEuclideanBC1Attachment
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set}
    {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    {actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present}
    (firstWeld : R133.UnifiedGeneratedActionFirstVariation actionWeld)
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
        (Euclidean.actConfiguration euclidean action background)
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
        (Euclidean.actConfiguration euclidean action background)
      ≡
      Carrier.effectivePotential (Present.bc1Carrier present)
        background

    bc2FirstVariationCovariant :
      ∀ action background tangent →
      DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact.firstVariation
        (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
        (Euclidean.actConfiguration euclidean action background)
        (actGlobalTangent action tangent)
      ≡
      DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact.firstVariation
        (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
        background tangent

open FiniteEuclideanBC1Attachment public

asR133EuclideanActionNaturality :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld
      EuclideanAction sequenceLimit limitLaws quotient division family euclidean} →
  FiniteEuclideanBC1Attachment
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld}
    firstWeld
    {EuclideanAction = EuclideanAction}
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family euclidean →
  E1R133.R133EuclideanActionNaturality firstWeld
asR133EuclideanActionNaturality
    {euclidean = euclidean} attachment = record
  { E1R133.R133EuclideanActionNaturality.EuclideanAction =
      _
  ; E1R133.R133EuclideanActionNaturality.actGlobalBackground =
      Euclidean.actConfiguration euclidean
  ; E1R133.R133EuclideanActionNaturality.actGlobalTangent =
      actGlobalTangent attachment
  ; E1R133.R133EuclideanActionNaturality.actStressBackground =
      actStressBackground attachment
  ; E1R133.R133EuclideanActionNaturality.actStressTangent =
      actStressTangent attachment
  ; E1R133.R133EuclideanActionNaturality.backgroundTransportEquivariant =
      backgroundTransportEquivariant attachment
  ; E1R133.R133EuclideanActionNaturality.tangentTransportEquivariant =
      tangentTransportEquivariant attachment
  ; E1R133.R133EuclideanActionNaturality.effectivePotentialCovariant =
      effectivePotentialCovariant attachment
  ; E1R133.R133EuclideanActionNaturality.bc2FirstVariationCovariant =
      bc2FirstVariationCovariant attachment
  }

wholeLatticeActionNowOwnsBC1BackgroundAction : Bool
wholeLatticeActionNowOwnsBC1BackgroundAction = true

remainingE1GeometryIsTangentActionAndNaturality : Bool
remainingE1GeometryIsTangentActionAndNaturality = true

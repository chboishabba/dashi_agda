{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1WholeLatticeSourceNaturalityExact where

------------------------------------------------------------------------
-- PREFERRED WHOLE-LATTICE E1 ROOT.
--
-- One source-local derivative-naturality package + equality of its background
-- action with the existing CMP119 OS1 whole-lattice action compiles to the
-- previous R143/R133 whole-lattice max-cut.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyE1SourceDerivativeNaturalityExact as SourceE1
import DASHI.Physics.Foundations.CMP119CosmologyE1ComponentPermutationExact as PermE1
import DASHI.Physics.Foundations.CMP119CosmologyE1R143LocalizedCompilerExact as R143E1
import DASHI.Physics.Foundations.CMP119CosmologyE1WholeLatticeLocalizedMaxCutExact as Whole
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
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity

record WholeLatticeSourceNaturalityE1
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
    {quotient : Quotient.RealQuotientConvergenceAuthority
      (RealLimit.Converges sequenceLimit)}
    {division : Division.RealDivisionAlgebra
      (RealLimit.canonicalCylinderAlgebra limitLaws) quotient}
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
    sourceNaturality :
      SourceE1.LiteralSourceDerivativeNaturality
        (Present.bc1Carrier present)
        (R143.asFirstVariationLinearity laws)
        EuclideanAction

    sourceBackgroundActionIsWholeLattice :
      ∀ action background →
      DASHI.Physics.Foundations.CMP119CosmologyE1DerivativeNaturalityExact.actConfiguration
        (SourceE1.derivativeNaturality sourceNaturality)
        action background
      ≡ Euclidean.actConfiguration euclidean action background

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
      ≡ actStressBackground action
          (R133.globalBackgroundToStressBackground firstWeld background)

    tangentTransportEquivariant :
      ∀ action tangent →
      R133.globalTangentToStressTangent firstWeld
        (DASHI.Physics.Foundations.CMP119CosmologyE1DerivativeNaturalityExact.actTangent
          (SourceE1.derivativeNaturality sourceNaturality)
          action tangent)
      ≡ actStressTangent action
          (R133.globalTangentToStressTangent firstWeld tangent)

open WholeLatticeSourceNaturalityE1 public

asWholeLatticeLocalizedE1MaxCut :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld firstWeld laws
      EuclideanAction sequenceLimit limitLaws quotient division family euclidean} →
  WholeLatticeSourceNaturalityE1
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld}
    firstWeld laws
    {EuclideanAction = EuclideanAction}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    family euclidean →
  Whole.WholeLatticeLocalizedE1MaxCut
    firstWeld laws family euclidean
asWholeLatticeLocalizedE1MaxCut data = record
  { Whole.WholeLatticeLocalizedE1MaxCut.localized = record
      { R143E1.R143LocalizedEuclideanCovariance.localized =
          PermE1.asLocalizedD1EuclideanCovariance
            (SourceE1.asComponentPermutationCovariance
              (sourceNaturality data))
      }
  ; Whole.WholeLatticeLocalizedE1MaxCut.localizedBackgroundActionIsWholeLattice =
      sourceBackgroundActionIsWholeLattice data
  ; Whole.WholeLatticeLocalizedE1MaxCut.actStressBackground =
      actStressBackground data
  ; Whole.WholeLatticeLocalizedE1MaxCut.actStressTangent =
      actStressTangent data
  ; Whole.WholeLatticeLocalizedE1MaxCut.backgroundTransportEquivariant =
      backgroundTransportEquivariant data
  ; Whole.WholeLatticeLocalizedE1MaxCut.tangentTransportEquivariant =
      tangentTransportEquivariant data
  }

wholeLatticeE1GlobalCovarianceIsCompilerOutput : Bool
wholeLatticeE1GlobalCovarianceIsCompilerOutput = true

remainingE1LeavesAreSourceTangentComponentGeometryDerivativeNaturalityAndR133Transport : Bool
remainingE1LeavesAreSourceTangentComponentGeometryDerivativeNaturalityAndR133Transport = true

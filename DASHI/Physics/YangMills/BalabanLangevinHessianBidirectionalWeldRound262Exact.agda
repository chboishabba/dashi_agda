{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact where

------------------------------------------------------------------------
-- ROUND262 / ROW-C BIDIRECTIONAL SAME-HESSIAN WELD
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Hess
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianGeneratorRowExact as Spatial
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianCurvatureIdentityExact as Temporal
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToWeightedInfluenceExact as WeightedBridge
import DASHI.Physics.YangMills.BalabanSharedMarkedMetricInfluenceExact as Influence
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToCurvatureDebtExact as Curv
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Debt
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom

record LiteralLangevinHessianBidirectionalWeld
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    langevin : Langevin.CompactLieLangevinFrameData
    literalDifferentiatedCommutator :
      Langevin.LangevinCommutatorIdentity langevin
    literalConnectionIsOnsiteAd :
      Langevin.connectionIsOnsiteAdTerm langevin

    -- No independent Site parameter: the influence row is definitionally on
    -- the exact site carrier of the literal Langevin frame.
    sites : List (Langevin.Site langevin)
    metric : Metric.NatMetricTriangle (Langevin.Site langevin)
    influence :
      Langevin.Site langevin → Langevin.Site langevin → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y
    rowDepth : Langevin.Site langevin → Nat

    symmetricLangevinRowIsCMP109116Hessian : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≡ Hess.weightedHessianPartial
          (Shared.hessianWeightedControl shared)
          scale volume root (rowDepth x)

    curvatureDebt : Nat → ℚ
    curvatureDebtNonnegative : ∀ n → 0ℚ ≤ curvatureDebt n
    sameHessianIsHeatDoobNegativeCurvatureShell : ∀ n →
      curvatureDebt n
      ≡ Shared.hessianInfluenceShell shared scale volume root n

open LiteralLangevinHessianBidirectionalWeld public

asSpatialIdentification :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root) →
  Spatial.LiteralHessianGeneratorRowIdentification
    Scale Volume Root (Langevin.Site (langevin dataSet))
asSpatialIdentification dataSet = record
  { Spatial.LiteralHessianGeneratorRowIdentification.shared = shared dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.scale = scale dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.volume = volume dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.root = root dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.sites = sites dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.metric = metric dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.influence = influence dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.influenceNonnegative =
      influenceNonnegative dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.rowDepth = rowDepth dataSet
  ; Spatial.LiteralHessianGeneratorRowIdentification.generatorRowIsMarkedHessianPartial =
      symmetricLangevinRowIsCMP109116Hessian dataSet
  }

spatialWeightedRowBound :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root)
    x →
  Sums.sumRational (sites dataSet)
    (λ y → Metric.metricWeight (metric dataSet) x y * influence dataSet x y)
  ≤ Shared.hessianAnalyticConstant (shared dataSet)
spatialWeightedRowBound dataSet =
  Spatial.weightedGeneratorRowBound (asSpatialIdentification dataSet)

spatialAllDysonRowsBound :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root)
    n x →
  Weighted.weightedPowerRow
    (WeightedBridge.asWeightedFiniteInfluence
      (Influence.asWeightedBridge
        (Spatial.asMetricInfluenceBridge (asSpatialIdentification dataSet))))
    n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet))
      (Agda.Builtin.Nat.suc n)
spatialAllDysonRowsBound dataSet =
  Spatial.allWeightedGeneratorPowersBound (asSpatialIdentification dataSet)

asTemporalIdentification :
  ∀ {Scale Volume Root} →
  LiteralLangevinHessianBidirectionalWeld Scale Volume Root →
  Temporal.LiteralCurvatureHessianShellIdentification Scale Volume Root
asTemporalIdentification dataSet = record
  { Temporal.LiteralCurvatureHessianShellIdentification.shared = shared dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.scale = scale dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.volume = volume dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.root = root dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.curvatureDebt =
      curvatureDebt dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.curvatureDebtNonnegative =
      curvatureDebtNonnegative dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.curvatureDebtIsPhysicalHessianShell =
      sameHessianIsHeatDoobNegativeCurvatureShell dataSet
  }

temporalUniformCurvatureDebt :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root)
    count →
  Debt.finiteCurvatureDebt
    (Curv.asGeometricNegativeCurvatureDebt
      (Temporal.asSharedHessianCurvatureDomination
        (asTemporalIdentification dataSet))) count
  ≤ Tail.tailFactor
      * Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
temporalUniformCurvatureDebt dataSet =
  Temporal.sameObjectCurvatureUniformDebt (asTemporalIdentification dataSet)

literalConnectionCancellationAvailable :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root) →
  Langevin.connectionIsOnsiteAdTerm (langevin dataSet)
literalConnectionCancellationAvailable dataSet =
  literalConnectionIsOnsiteAd dataSet

round262BidiCompilerLevel : ProofLevel
round262BidiCompilerLevel = machineChecked

round262LiteralSourceRealizationLevel : ProofLevel
round262LiteralSourceRealizationLevel = conditional

round262ClayClosureLevel : ProofLevel
round262ClayClosureLevel = conditional

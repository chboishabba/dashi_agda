{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact where

------------------------------------------------------------------------
-- ROUND262/R264/R266/R269 / ROW-C BIDIRECTIONAL SAME-HESSIAN WELD
--
-- R262: one literal Langevin/source carrier feeds spatial and temporal users.
-- R264: exact weighted-partial equality weakened to the one-sided row bound.
-- R266: rational influence must majorize the actual real typed action Hessian.
-- R269: R268 now constructs that entrywise majorant from anchored R260 debt, so
--       this record is a consumer ABI rather than a separate source theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact as Metric
import DASHI.Physics.YangMills.BalabanSharedMarkedMetricInfluenceExact as Influence
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianCurvatureIdentityExact as Temporal
import DASHI.Physics.YangMills.BalabanFiniteWeightedInfluencePowerExact as Weighted
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianToWeightedInfluenceExact as WeightedBridge
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

    langevin : Langevin.TypedLangevinCommutatorData ℝ

    sites : List (Langevin.Site (Langevin.frame langevin))
    metric : Metric.NatMetricTriangle (Langevin.Site (Langevin.frame langevin))
    influence :
      Langevin.Site (Langevin.frame langevin) →
      Langevin.Site (Langevin.frame langevin) → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y

    embedding : Embed.OrderedRationalRealRingEmbedding

    actionHessianAbsBelowInfluence : ∀ x y →
      absℝ (Langevin.actionHessianEntry langevin x y)
      ≤ℝ Embed.embed embedding (influence x y)

    symmetricLangevinWeightedRowBelowSharedHessian : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≤ Shared.hessianAnalyticConstant shared

    curvatureDebt : Nat → ℚ
    curvatureDebtNonnegative : ∀ n → 0ℚ ≤ curvatureDebt n
    sameHessianIsHeatDoobNegativeCurvatureShell : ∀ n →
      curvatureDebt n
      ≡ Shared.hessianInfluenceShell shared scale volume root n

open LiteralLangevinHessianBidirectionalWeld public

literalCommutatorIsHessianPlusConnection :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root) →
  ∀ x y →
  Langevin.commutatorEntry (langevin dataSet) x y
  ≡ Langevin.add (langevin dataSet)
      (Langevin.actionHessianEntry (langevin dataSet) x y)
      (Langevin.connectionEntry (langevin dataSet) x y)
literalCommutatorIsHessianPlusConnection dataSet =
  Langevin.commutatorEntryIsHessianPlusConnection (langevin dataSet)

asMetricInfluenceBridge :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root) →
  Influence.SharedMarkedMetricInfluenceBridge
    Scale Volume Root (Langevin.Site (Langevin.frame (langevin dataSet)))
asMetricInfluenceBridge dataSet = record
  { Influence.SharedMarkedMetricInfluenceBridge.shared = shared dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.scale = scale dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.volume = volume dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.root = root dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.sites = sites dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.metric = metric dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influence = influence dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influenceNonnegative = influenceNonnegative dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.weightedGeneratorRowBelowSharedHessian =
      symmetricLangevinWeightedRowBelowSharedHessian dataSet
  }

spatialAllDysonRowsBound :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root)
    n x →
  Weighted.weightedPowerRow
    (WeightedBridge.asWeightedFiniteInfluence
      (Influence.asWeightedBridge (asMetricInfluenceBridge dataSet)))
    n x
  ≤ Power.rationalPower
      (Shared.hessianAnalyticConstant (shared dataSet))
      (Agda.Builtin.Nat.suc n)
spatialAllDysonRowsBound dataSet =
  Influence.metricWeightedPowerRowBound (asMetricInfluenceBridge dataSet)

asTemporalIdentification :
  ∀ {Scale Volume Root} →
  LiteralLangevinHessianBidirectionalWeld Scale Volume Root →
  Temporal.LiteralCurvatureHessianShellIdentification Scale Volume Root
asTemporalIdentification dataSet = record
  { Temporal.LiteralCurvatureHessianShellIdentification.shared = shared dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.scale = scale dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.volume = volume dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.root = root dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.curvatureDebt = curvatureDebt dataSet
  ; Temporal.LiteralCurvatureHessianShellIdentification.curvatureDebtNonnegative = curvatureDebtNonnegative dataSet
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
  ≤ Tail.tailFactor * Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
temporalUniformCurvatureDebt dataSet =
  Temporal.sameObjectCurvatureUniformDebt (asTemporalIdentification dataSet)

literalConnectionCancellationAvailable :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root) →
  Langevin.connectionIsOnsiteAdTerm (Langevin.frame (langevin dataSet))
literalConnectionCancellationAvailable dataSet =
  Langevin.connectionEntryIsOnsiteAd (langevin dataSet)

round262BidiCompilerLevel : ProofLevel
round262BidiCompilerLevel = machineChecked

round264LeastPrivilegeSpatialCompilerLevel : ProofLevel
round264LeastPrivilegeSpatialCompilerLevel =
  Influence.sharedMarkedMetricToAllWeightedPowerRowsLevel

round266TypedSameObjectInfluenceCompilerLevel : ProofLevel
round266TypedSameObjectInfluenceCompilerLevel =
  Langevin.typedLangevinCommutatorCompilerLevel

-- Historical status alias: source construction is now concretely split by R269
-- into S1/S2/S3 rather than treated as one opaque payment.
round262LiteralSourceRealizationLevel : ProofLevel
round262LiteralSourceRealizationLevel = conditional

round262ClayClosureLevel : ProofLevel
round262ClayClosureLevel = conditional

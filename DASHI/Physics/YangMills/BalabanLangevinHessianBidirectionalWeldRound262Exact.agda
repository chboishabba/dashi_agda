{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact where

------------------------------------------------------------------------
-- ROUND262/R264 / ROW-C BIDIRECTIONAL SAME-HESSIAN WELD
--
-- R262 forced the spatial and temporal Row-C consumers onto ONE literal
-- Langevin/source carrier.  R264 now removes one remaining overcharge:
--
--   weighted generator row = one CMP116 weighted partial
--
-- was stronger than the downstream finite-speed/Dyson consumer needs.
-- The existing least-privilege metric influence compiler requires only
--
--   weighted generator row <= shared CMP116 Hessian constant.
--
-- So this owner now stores exactly that one-sided same-object domination.
-- No rowDepth and no exact partial-sum equality remain on the preferred path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
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

    -- Least-privilege spatial source payment.  The finite-speed/Dyson compiler
    -- needs only this domination, not equality with a chosen finite shell
    -- partial sum.  It must still concern the SAME literal derivative generator
    -- represented by `langevin` and the SAME marked source represented by
    -- `shared`; that physical identification remains the live source seam.
    symmetricLangevinWeightedRowBelowSharedHessian : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≤ Shared.hessianAnalyticConstant shared

    -- Temporal projection from the SAME marked source object.
    curvatureDebt : Nat → ℚ
    curvatureDebtNonnegative : ∀ n → 0ℚ ≤ curvatureDebt n
    sameHessianIsHeatDoobNegativeCurvatureShell : ∀ n →
      curvatureDebt n
      ≡ Shared.hessianInfluenceShell shared scale volume root n

open LiteralLangevinHessianBidirectionalWeld public

------------------------------------------------------------------------
-- Projection 1: same literal source -> least-privilege spatial compiler.
------------------------------------------------------------------------

asMetricInfluenceBridge :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root) →
  Influence.SharedMarkedMetricInfluenceBridge
    Scale Volume Root (Langevin.Site (langevin dataSet))
asMetricInfluenceBridge dataSet = record
  { Influence.SharedMarkedMetricInfluenceBridge.shared = shared dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.scale = scale dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.volume = volume dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.root = root dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.sites = sites dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.metric = metric dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influence = influence dataSet
  ; Influence.SharedMarkedMetricInfluenceBridge.influenceNonnegative =
      influenceNonnegative dataSet
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

------------------------------------------------------------------------
-- Projection 2: same literal source -> temporal curvature-debt compiler.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Exact compact-Lie connection cancellation remains downstream once identified.
------------------------------------------------------------------------

literalConnectionCancellationAvailable :
  ∀ {Scale Volume Root}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root) →
  Langevin.connectionIsOnsiteAdTerm (langevin dataSet)
literalConnectionCancellationAvailable dataSet =
  literalConnectionIsOnsiteAd dataSet

round262BidiCompilerLevel : ProofLevel
round262BidiCompilerLevel = machineChecked

round264LeastPrivilegeSpatialCompilerLevel : ProofLevel
round264LeastPrivilegeSpatialCompilerLevel =
  Influence.sharedMarkedMetricToAllWeightedPowerRowsLevel

-- Still physical/source debt: instantiate one literal source object satisfying
-- the differentiated commutator, its symmetric-Hessian identification, the one
-- least-privilege weighted-row domination, and the temporal same-density shell.
round262LiteralSourceRealizationLevel : ProofLevel
round262LiteralSourceRealizationLevel = conditional

round262ClayClosureLevel : ProofLevel
round262ClayClosureLevel = conditional

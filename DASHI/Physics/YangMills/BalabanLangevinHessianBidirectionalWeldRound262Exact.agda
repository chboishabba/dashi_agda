{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact where

------------------------------------------------------------------------
-- ROUND262/R264/R266 / ROW-C BIDIRECTIONAL SAME-HESSIAN WELD
--
-- R262: one literal Langevin/source carrier feeds spatial and temporal users.
-- R264: weaken exact weighted-partial equality to the one-sided row bound the
--       propagation consumer actually needs.
-- R266: remove the remaining adjacency loophole: the rational influence matrix
--       must majorize the absolute REAL action-Hessian entries of the exact
--       typed Langevin commutator carrier.
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

    -- Typed real-coefficient commutator: C4a decomposition and C4b
    -- symmetric=action-Hessian are now proof-relevant fields of this object.
    langevin : Langevin.TypedLangevinCommutatorData ℝ

    -- No independent Site parameter: all spatial data live on the exact site
    -- carrier of the typed literal Langevin frame.
    sites : List (Langevin.Site (Langevin.frame langevin))
    metric : Metric.NatMetricTriangle (Langevin.Site (Langevin.frame langevin))
    influence :
      Langevin.Site (Langevin.frame langevin) →
      Langevin.Site (Langevin.frame langevin) → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y

    -- Exact rational-to-real bridge used to compare the physical Hessian entry
    -- with the nonnegative rational influence majorant.
    embedding : Embed.OrderedRationalRealRingEmbedding

    -- SAME-OBJECT condition: the finite influence matrix is not merely near a
    -- Hessian-named object; it majorizes the actual action-Hessian entries of
    -- this exact typed differentiated Langevin commutator.
    actionHessianAbsBelowInfluence : ∀ x y →
      absℝ (Langevin.actionHessianEntry langevin x y)
      ≤ℝ Embed.embed embedding (influence x y)

    -- Least-privilege weighted row payment.  Downstream all-power estimates are
    -- compiler-owned and require no exact shell-partial equality.
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
-- Typed commutator consequence: no opaque C4a/C4b socket remains here.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Projection 1: same literal source -> least-privilege spatial compiler.
------------------------------------------------------------------------

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
  Langevin.connectionIsOnsiteAdTerm
    (Langevin.frame (langevin dataSet))
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

-- Still physical/source debt: instantiate the typed real commutator on the
-- literal Balaban effective density and prove its actual Hessian entries admit
-- the same rational weighted majorant used by the shared source shell.
round262LiteralSourceRealizationLevel : ProofLevel
round262LiteralSourceRealizationLevel = conditional

round262ClayClosureLevel : ProofLevel
round262ClayClosureLevel = conditional

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact where

------------------------------------------------------------------------
-- ROUND262 / ROW-C BIDIRECTIONAL SAME-HESSIAN WELD
--
-- R261 correctly split the remaining spatial source debt into
--
--   C4a : literal differentiated compact-group Langevin commutator;
--   C4b : its symmetric nonlocal part is the literal CMP109/CMP116 Hessian.
--
-- The historical spatial and temporal consumers, however, still accepted
-- independent physical witnesses.  That leaves a WrongType hole: one could
-- pay the generator-row seam with one object and the Heat/Doob curvature seam
-- with a neighbouring Hessian object.
--
-- This module removes that duplication.  One physical dataset owns ONE shared
-- marked CMP109/CMP116 Hessian carrier and projects it in both directions:
--
--   same Hessian -> spatial weighted generator row -> all Dyson rows;
--   same Hessian -> temporal negative-curvature shell -> uniform debt.
--
-- It does NOT manufacture C4a/C4b.  The two source-realisation maps below are
-- exactly the remaining physical obligations, now forced to share the same
-- source/density/scale/volume/root carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
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
    (Scale Volume Root Site : Set) : Set₁ where
  field
    -- ONE literal source carrier.  Both consumers below are indexed by these
    -- exact coordinates, so a neighbouring density/scale cannot silently pay.
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    -- C4a carrier.  The source must instantiate the literal differentiated
    -- compact-group Langevin commutator and onsite-ad decomposition here.
    langevin : Langevin.CompactLieLangevinFrameData
    literalDifferentiatedCommutator :
      Langevin.LangevinCommutatorIdentity langevin
    literalConnectionIsOnsiteAd :
      Langevin.connectionIsOnsiteAdTerm langevin

    -- Spatial realization of the SAME symmetric Hessian.
    sites : List Site
    metric : Metric.NatMetricTriangle Site
    influence : Site → Site → ℚ
    influenceNonnegative : ∀ x y → 0ℚ ≤ influence x y
    rowDepth : Site → Nat

    symmetricLangevinRowIsCMP109116Hessian : ∀ x →
      Sums.sumRational sites
        (λ y → Metric.metricWeight metric x y * influence x y)
      ≡ Hess.weightedHessianPartial
          (Shared.hessianWeightedControl shared)
          scale volume root (rowDepth x)

    -- Temporal realization of that SAME source Hessian on the same density.
    curvatureDebt : Nat → ℚ
    curvatureDebtNonnegative : ∀ n → 0ℚ ≤ curvatureDebt n
    sameHessianIsHeatDoobNegativeCurvatureShell : ∀ n →
      curvatureDebt n
      ≡ Shared.hessianInfluenceShell shared scale volume root n

open LiteralLangevinHessianBidirectionalWeld public

------------------------------------------------------------------------
-- Projection 1: same physical Hessian -> spatial generator-row compiler.
------------------------------------------------------------------------

asSpatialIdentification :
  ∀ {Scale Volume Root Site} →
  LiteralLangevinHessianBidirectionalWeld Scale Volume Root Site →
  Spatial.LiteralHessianGeneratorRowIdentification Scale Volume Root Site
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
  ∀ {Scale Volume Root Site}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root Site)
    x →
  Sums.sumRational (sites dataSet)
    (λ y → Metric.metricWeight (metric dataSet) x y * influence dataSet x y)
  ≤ Shared.hessianAnalyticConstant (shared dataSet)
spatialWeightedRowBound dataSet =
  Spatial.weightedGeneratorRowBound (asSpatialIdentification dataSet)

spatialAllDysonRowsBound :
  ∀ {Scale Volume Root Site}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root Site)
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

------------------------------------------------------------------------
-- Projection 2: same physical Hessian -> temporal curvature-debt compiler.
------------------------------------------------------------------------

asTemporalIdentification :
  ∀ {Scale Volume Root Site} →
  LiteralLangevinHessianBidirectionalWeld Scale Volume Root Site →
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
  ∀ {Scale Volume Root Site}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root Site)
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
-- Exact connection cancellation is paid from the SAME literal Langevin frame.
------------------------------------------------------------------------

literalConnectionCancellationAvailable :
  ∀ {Scale Volume Root Site}
    (dataSet : LiteralLangevinHessianBidirectionalWeld Scale Volume Root Site) →
  Langevin.connectionIsOnsiteAdTerm (langevin dataSet)
literalConnectionCancellationAvailable dataSet =
  literalConnectionIsOnsiteAd dataSet

------------------------------------------------------------------------
-- Status firewall.
------------------------------------------------------------------------

round262BidiCompilerLevel : ProofLevel
round262BidiCompilerLevel = machineChecked

-- Still physical/source debt: instantiate one literal source object satisfying
-- the differentiated commutator and both same-Hessian realization maps.
round262LiteralSourceRealizationLevel : ProofLevel
round262LiteralSourceRealizationLevel = conditional

-- No Clay claim is implied by compiler closure.
round262ClayClosureLevel : ProofLevel
round262ClayClosureLevel = conditional

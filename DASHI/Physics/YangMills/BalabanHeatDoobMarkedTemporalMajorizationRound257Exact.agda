{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobMarkedTemporalMajorizationRound257Exact where

------------------------------------------------------------------------
-- ROUND257 / EXACT REAL HEAT-DOOB HESSIAN -> MARKED RATIONAL DEBT
--
-- The old temporal capstone carried a physical rational inequality
--
--   actualDebt <= staticDebt + covarianceDebt.
--
-- That is stronger than the real consumer needs and duplicates standard
-- triangle/expectation algebra.  On the exact same-density carrier we instead
-- use
--
--   Hess V_t = E_t[Hess V] - Cov_t(grad V,grad V),
--
-- bound the conditional static term by the CMP116 hessian shell, bound the
-- covariance term by its already-rational marked first-gradient debt, and DEFINE
--
--   D_t = H_t + C_t.
--
-- R253 then proves that D_t majorizes the actual real Heat/Doob Hessian.  The
-- historical rational shell summation can consume D_t with a reflexive split.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanHeatDoobFromSameDensityExpectationRound108Exact as Heat
import DASHI.Physics.YangMills.BalabanHeatDoobSameDensityLogHessianRound103Exact as LogHeat
import DASHI.Physics.YangMills.BalabanHeatDoobExpectationContractionRound254Exact as Contract
import DASHI.Physics.YangMills.BalabanHeatDoobRationalCurvatureMajorantRound253Exact as Major
import DASHI.Physics.YangMills.BalabanCMP116FirstGradientCovarianceInstantiationRound102Exact as FirstCov
import DASHI.Physics.YangMills.BalabanCMP116FirstGradientSharedMarkedExact as First
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Cov
import DASHI.Physics.YangMills.BalabanHeatDoobHessianCovarianceDebtExact as Legacy
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Curv
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail

record SameDensityMarkedTemporalMajorization
    {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier}
    (heat : Heat.SameDensityHeatExpectation carrier)
    (contraction : Contract.NormalizedHeatTiltExpectationContraction heat)
    (embedding : Embed.OrderedRationalRealRingEmbedding)
    (Scale Volume Root : Set) : Set₁ where
  field
    covarianceData :
      FirstCov.CMP116TemporalFirstGradientCovariance Scale Volume Root

    timeAtDepth : Nat → Heat.Time heat
    backgroundAtDepth : Nat → Source.Background (Carrier.source carrier)
    uAtDepth vAtDepth : Nat → Source.Tangent (Carrier.source carrier)

    pointwiseStaticHessianMajorized : ∀ depth y →
      absℝ
        (Carrier.cmp116PhysicalMarkedHessian carrier y
          (uAtDepth depth) (vAtDepth depth))
      ≤ℝ
      Embed.embed embedding
        (Shared.hessianInfluenceShell
          (First.shared (FirstCov.firstGradient covarianceData))
          (FirstCov.scale covarianceData)
          (FirstCov.volume covarianceData)
          (FirstCov.root covarianceData)
          depth)

    covarianceRealMajorized : ∀ depth →
      absℝ
        (LogHeat.conditionalGradientCovariance
          (Heat.asRound103HeatDoobCalculus heat)
          (timeAtDepth depth)
          (backgroundAtDepth depth)
          (uAtDepth depth)
          (vAtDepth depth))
      ≤ℝ Embed.embed embedding
        (FirstCov.covarianceDebt covarianceData depth)

open SameDensityMarkedTemporalMajorization public

shared :
  ∀ {carrier heat contraction embedding Scale Volume Root} →
  SameDensityMarkedTemporalMajorization
    {carrier = carrier} heat contraction embedding Scale Volume Root →
  Shared.SharedMarkedAnalyticShellControl Scale Volume Root
shared dataSet = First.shared (FirstCov.firstGradient (covarianceData dataSet))

staticDebt :
  ∀ {carrier heat contraction embedding Scale Volume Root} →
  SameDensityMarkedTemporalMajorization
    {carrier = carrier} heat contraction embedding Scale Volume Root →
  Nat → ℚ
staticDebt dataSet depth =
  Shared.hessianInfluenceShell
    (shared dataSet)
    (FirstCov.scale (covarianceData dataSet))
    (FirstCov.volume (covarianceData dataSet))
    (FirstCov.root (covarianceData dataSet))
    depth

staticPointwiseMajorantAt :
  ∀ {carrier heat contraction embedding Scale Volume Root}
    (dataSet : SameDensityMarkedTemporalMajorization
      {carrier = carrier} heat contraction embedding Scale Volume Root)
    depth →
  Contract.PointwiseStaticHessianMajorant heat contraction embedding
staticPointwiseMajorantAt dataSet depth = record
  { Contract.PointwiseStaticHessianMajorant.time = timeAtDepth dataSet depth
  ; Contract.PointwiseStaticHessianMajorant.background = backgroundAtDepth dataSet depth
  ; Contract.PointwiseStaticHessianMajorant.u = uAtDepth dataSet depth
  ; Contract.PointwiseStaticHessianMajorant.v = vAtDepth dataSet depth
  ; Contract.PointwiseStaticHessianMajorant.rationalBound = staticDebt dataSet depth
  ; Contract.PointwiseStaticHessianMajorant.pointwiseStaticHessianBound =
      pointwiseStaticHessianMajorized dataSet depth
  }

asRationalMajorizedSplitAt :
  ∀ {carrier heat contraction embedding Scale Volume Root}
    (dataSet : SameDensityMarkedTemporalMajorization
      {carrier = carrier} heat contraction embedding Scale Volume Root)
    depth →
  Major.RationalMajorizedHeatDoobSplit embedding
asRationalMajorizedSplitAt {carrier} {heat} {contraction} {embedding}
    dataSet depth =
  let
    calculus = Heat.asRound103HeatDoobCalculus heat
    time = timeAtDepth dataSet depth
    background = backgroundAtDepth dataSet depth
    u = uAtDepth dataSet depth
    v = vAtDepth dataSet depth
  in record
    { Major.RationalMajorizedHeatDoobSplit.actual =
        Heat.heatDoobHessian heat time background u v
    ; Major.RationalMajorizedHeatDoobSplit.static =
        LogHeat.conditionalExpectedStaticHessian calculus time background u v
    ; Major.RationalMajorizedHeatDoobSplit.covariance =
        LogHeat.conditionalGradientCovariance calculus time background u v
    ; Major.RationalMajorizedHeatDoobSplit.staticDebt = staticDebt dataSet depth
    ; Major.RationalMajorizedHeatDoobSplit.covarianceDebt =
        FirstCov.covarianceDebt (covarianceData dataSet) depth
    ; Major.RationalMajorizedHeatDoobSplit.staticDebtNonnegative =
        Shared.hessianInfluenceShellNonnegative
          (shared dataSet)
          (FirstCov.scale (covarianceData dataSet))
          (FirstCov.volume (covarianceData dataSet))
          (FirstCov.root (covarianceData dataSet))
          depth
    ; Major.RationalMajorizedHeatDoobSplit.covarianceDebtNonnegative =
        FirstCov.covarianceDebtNonnegative (covarianceData dataSet) depth
    ; Major.RationalMajorizedHeatDoobSplit.exactStaticMinusCovariance =
        LogHeat.heatDoobHessianIsStaticMinusCovariance calculus time background u v
    ; Major.RationalMajorizedHeatDoobSplit.staticAbsMajorized =
        Contract.conditionalStaticHessianMajorized
          (staticPointwiseMajorantAt dataSet depth)
    ; Major.RationalMajorizedHeatDoobSplit.covarianceAbsMajorized =
        covarianceRealMajorized dataSet depth
    }

actualRationalDebt :
  ∀ {carrier heat contraction embedding Scale Volume Root} →
  SameDensityMarkedTemporalMajorization
    {carrier = carrier} heat contraction embedding Scale Volume Root →
  Nat → ℚ
actualRationalDebt dataSet depth =
  Major.actualDebt (asRationalMajorizedSplitAt dataSet depth)

actualRealHessianMajorized :
  ∀ {carrier heat contraction embedding Scale Volume Root}
    (dataSet : SameDensityMarkedTemporalMajorization
      {carrier = carrier} heat contraction embedding Scale Volume Root)
    depth →
  absℝ
    (Heat.heatDoobHessian heat
      (timeAtDepth dataSet depth)
      (backgroundAtDepth dataSet depth)
      (uAtDepth dataSet depth)
      (vAtDepth dataSet depth))
  ≤ℝ Embed.embed embedding (actualRationalDebt dataSet depth)
actualRealHessianMajorized dataSet depth =
  Major.actualAbsMajorized (asRationalMajorizedSplitAt dataSet depth)

asLegacyTemporalDebt :
  ∀ {carrier heat contraction embedding Scale Volume Root} →
  SameDensityMarkedTemporalMajorization
    {carrier = carrier} heat contraction embedding Scale Volume Root →
  Legacy.HeatDoobHessianCovarianceDebt Scale Volume Root
asLegacyTemporalDebt dataSet =
  let cov = FirstCov.asTemporalGradientCovariance (covarianceData dataSet)
  in record
    { Legacy.HeatDoobHessianCovarianceDebt.shared = shared dataSet
    ; Legacy.HeatDoobHessianCovarianceDebt.scale = FirstCov.scale (covarianceData dataSet)
    ; Legacy.HeatDoobHessianCovarianceDebt.volume = FirstCov.volume (covarianceData dataSet)
    ; Legacy.HeatDoobHessianCovarianceDebt.root = FirstCov.root (covarianceData dataSet)
    ; Legacy.HeatDoobHessianCovarianceDebt.staticHessianDebt = staticDebt dataSet
    ; Legacy.HeatDoobHessianCovarianceDebt.covarianceDebt =
        FirstCov.covarianceDebt (covarianceData dataSet)
    ; Legacy.HeatDoobHessianCovarianceDebt.actualNegativeHessianDebt = actualRationalDebt dataSet
    ; Legacy.HeatDoobHessianCovarianceDebt.staticNonnegative =
        λ depth → Shared.hessianInfluenceShellNonnegative
          (shared dataSet)
          (FirstCov.scale (covarianceData dataSet))
          (FirstCov.volume (covarianceData dataSet))
          (FirstCov.root (covarianceData dataSet)) depth
    ; Legacy.HeatDoobHessianCovarianceDebt.covarianceNonnegative =
        FirstCov.covarianceDebtNonnegative (covarianceData dataSet)
    ; Legacy.HeatDoobHessianCovarianceDebt.actualNonnegative =
        λ depth → Major.actualDebtNonnegative (asRationalMajorizedSplitAt dataSet depth)
    ; Legacy.HeatDoobHessianCovarianceDebt.heatDoobSplit = λ depth → ℚP.≤-refl
    ; Legacy.HeatDoobHessianCovarianceDebt.staticBelowMarkedHessian = λ depth → ℚP.≤-refl
    ; Legacy.HeatDoobHessianCovarianceDebt.covarianceAmplitude =
        Cov.temporalCovarianceAmplitude cov
    ; Legacy.HeatDoobHessianCovarianceDebt.covarianceAmplitudeNonnegative =
        Cov.temporalCovarianceAmplitudeNonnegative cov
    ; Legacy.HeatDoobHessianCovarianceDebt.covarianceGeometricHalf =
        Cov.temporalCovarianceGeometricHalf cov
    }

finiteActualRationalDebtUniform :
  ∀ {carrier heat contraction embedding Scale Volume Root}
    (dataSet : SameDensityMarkedTemporalMajorization
      {carrier = carrier} heat contraction embedding Scale Volume Root)
    count →
  Curv.finiteCurvatureDebt
    (Legacy.asGeometricNegativeCurvatureDebt (asLegacyTemporalDebt dataSet)) count
  ≤ Tail.tailFactor * Legacy.combinedAmplitude (asLegacyTemporalDebt dataSet)
finiteActualRationalDebtUniform dataSet =
  Legacy.finiteActualHeatDoobDebtUniform (asLegacyTemporalDebt dataSet)

markedTemporalRealToRationalCompilerLevel : ProofLevel
markedTemporalRealToRationalCompilerLevel = machineChecked

markedTemporalScalarAnalysisLevel : ProofLevel
markedTemporalScalarAnalysisLevel = standardImported

-- Exact remaining source-facing seams of this owner.  These are deliberately
-- separated from the older rational shell-equality receipt: one is a real
-- pointwise Hessian majorization and the other is the exact same-density
-- covariance majorized by the marked first-gradient debt.
literalCMP116RealHessianMarkedShellMajorizationLevel : ProofLevel
literalCMP116RealHessianMarkedShellMajorizationLevel = conditional

literalHeatDoobCovarianceMarkedFirstGradientMajorizationLevel : ProofLevel
literalHeatDoobCovarianceMarkedFirstGradientMajorizationLevel = conditional

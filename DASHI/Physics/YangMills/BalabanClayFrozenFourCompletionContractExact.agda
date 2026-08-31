module DASHI.Physics.YangMills.BalabanClayFrozenFourCompletionContractExact where

------------------------------------------------------------------------
-- FROZEN RESEARCH SCOREBOARD: FOUR MEANS FOUR PHYSICAL THEOREMS
--
-- This file is deliberately not another decomposition round.  It prevents a
-- future implementation from decrementing the research count merely because
-- one downstream compiler, source transcription, or formal-foundation layer
-- was completed.
--
-- A row closes only when an inhabitant of its physical completion predicate is
-- supplied on the literal same-object carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_)
open import Data.Product using (_×_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffBetaLaw as BetaLaw
import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory as Trajectory
import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra as Interval
import DASHI.Physics.YangMills.BalabanRenormalisedCouplingExistence as Renorm
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact as HeatDoob
import DASHI.Physics.YangMills.CompactLieHeatDoobRicciReserveDebtExact as Reserve
import DASHI.Physics.YangMills.BalabanPolchinskiMultiscaleLSIBridgeExact as BBD

------------------------------------------------------------------------
-- A. POSITIVE / TUNED LITERAL BETA TRAJECTORY
------------------------------------------------------------------------

record LiteralCompactSimplePositiveBetaCompletion : Set₁ where
  field
    construction : Renorm.BalabanRenormalisedCouplingConstruction

    lowerSlope upperSlope : ℝ
    lowerSlopePositive : 0ℝ <ℝ lowerSlope
    lowerSlopeBelowUpperSlope : lowerSlope ≤ℝ upperSlope

    lowerLinear upperLinear : Nat → ℝ
    lowerLinearZero : lowerLinear zero ≡ 0ℝ
    upperLinearZero : upperLinear zero ≡ 0ℝ
    lowerLinearStep : ∀ n →
      lowerLinear (suc n) ≡ lowerLinear n +ℝ lowerSlope
    upperLinearStep : ∀ n →
      upperLinear (suc n) ≡ upperLinear n +ℝ upperSlope

    betaTerminalTailBilateral :
      ∀ K k n → k + n ≡ K →
      lowerLinear n ≤ℝ
        Interval.intervalSum
          (Trajectory.betaCorrection
            (BetaLaw.step (Renorm.dynamics construction K)))
          k n
      ×
      Interval.intervalSum
        (Trajectory.betaCorrection
          (BetaLaw.step (Renorm.dynamics construction K)))
        k n
        ≤ℝ upperLinear n

open LiteralCompactSimplePositiveBetaCompletion public

rowAHasRenormalisedTrajectory :
  LiteralCompactSimplePositiveBetaCompletion →
  Renorm.BalabanRenormalisedCouplingConstruction
rowAHasRenormalisedTrajectory = construction

------------------------------------------------------------------------
-- C. EVIDENCE-BEARING COMPACT-GROUP HEAT/DOOB COMPLETION
------------------------------------------------------------------------
--
-- Round108 hardening: the old form stored
--
--   literalSameDensityIdentification : Set
--   physicalCovariantInfluencePropagation : Set
--   uniformExponentialConnectedClustering : Set
--
-- which names proposition TYPES but does not require inhabitants of them.  That
-- is weaker than the frozen scoreboard contract intended.  Each physical leaf
-- now has an explicit predicate/type AND a witness inhabiting it.  No existing
-- theorem constructor depended on the weaker projections.
------------------------------------------------------------------------

record SameDensityCompactLieHeatDoobMassGapCompletion
    (dataSet : HeatDoob.HeatDoobMultiscaleLSIData) : Set₁ where
  field
    SameDensityIdentification : Set
    literalSameDensityIdentification : SameDensityIdentification

    reserveAndHessianDebt : Reserve.RicciReserveHessianDebtData dataSet

    CovariantInfluencePropagation : Set
    physicalCovariantInfluencePropagation : CovariantInfluencePropagation

    ExponentialConnectedClustering : Set
    uniformExponentialConnectedClustering : ExponentialConnectedClustering

open SameDensityCompactLieHeatDoobMassGapCompletion public

record AlternateBBDGaugeChartCompletion
    (RGState Field Scale Potential CovarianceOperator HessianForm Bound : Set)
    : Set₁ where
  field
    bridge : BBD.BalabanPolchinskiSameObjectBridge
      RGState Field Scale Potential CovarianceOperator HessianForm Bound
    weightedPolchinskiCriterionFinite :
      BBD.polchinskiIntegralFinite (BBD.criterion bridge)

open AlternateBBDGaugeChartCompletion public

rowCHeatDoobGivesLSI :
  ∀ {dataSet}
    (completion : SameDensityCompactLieHeatDoobMassGapCompletion dataSet) →
  HeatDoob.LogSobolev dataSet
    (Reserve.history (reserveAndHessianDebt completion))
rowCHeatDoobGivesLSI completion =
  Reserve.ricciReserveDebtGivesLSI (reserveAndHessianDebt completion)

------------------------------------------------------------------------
-- SCOREBOARD AUTHORITY
------------------------------------------------------------------------

frozenClayResearchFamilyCount : Nat
frozenClayResearchFamilyCount = 4

rowACompletionLevel : ProofLevel
rowACompletionLevel = conditional

rowBCompletionLevel : ProofLevel
rowBCompletionLevel = conditional

rowCCompletionLevel : ProofLevel
rowCCompletionLevel = conditional

rowDCompletionLevel : ProofLevel
rowDCompletionLevel = conditional

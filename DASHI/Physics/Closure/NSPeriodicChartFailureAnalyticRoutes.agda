module DASHI.Physics.Closure.NSPeriodicChartFailureAnalyticRoutes where

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicChartFailureCoverage as Coverage
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Analytic owners for the three failed-chart branches.
--
-- Bad Gamma, bad tail and excessive size are not accepted as marker routes.
-- Each branch must provide a literal vorticity-expenditure estimate, a finite
-- budget, and transport of that estimate to direct BKM control.  The module then
-- constructs the exact failure-case package consumed by the exhaustive selector.
------------------------------------------------------------------------

record PeriodicChartFailureAnalyticInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (State Shell : Set i) : Set (lsuc i) where
  field
    LargePacket : Shell → State → Set i
    GammaGood TailGood SizeGood : Shell → State → Set i
    ChartAdmissible : Shell → State → Set i
    DirectBKMControlled : State → Set i

    gammaDecision : ∀ shell u →
      GammaGood shell u ⊎ (GammaGood shell u → ⊥)
    tailDecision : ∀ shell u →
      TailGood shell u ⊎ (TailGood shell u → ⊥)
    sizeDecision : ∀ shell u →
      SizeGood shell u ⊎ (SizeGood shell u → ⊥)

    chartFromAllConditions : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      TailGood shell u →
      SizeGood shell u →
      ChartAdmissible shell u

    vorticityExpenditure : State → Scalar A
    gammaFailureBudget tailFailureBudget sizeFailureBudget :
      Shell → State → Scalar A

    BudgetFinite : Scalar A → Set i
    VorticityExpenditureFinite : State → Set i

    boundedByFiniteBudgetImpliesVorticityFinite : ∀ u budget →
      _≤_ A (vorticityExpenditure u) budget →
      BudgetFinite budget →
      VorticityExpenditureFinite u

    finiteVorticityImpliesDirectBKM : ∀ u →
      VorticityExpenditureFinite u →
      DirectBKMControlled u

    -- Bad Gamma: angular depletion or another explicit incoherence estimate.
    badGammaVorticityEstimate : ∀ shell u →
      LargePacket shell u →
      (GammaGood shell u → ⊥) →
      _≤_ A (vorticityExpenditure u) (gammaFailureBudget shell u)

    badGammaBudgetFinite : ∀ shell u →
      LargePacket shell u →
      (GammaGood shell u → ⊥) →
      BudgetFinite (gammaFailureBudget shell u)

    -- Bad tail: a proved secondary-chart/diffuse estimate must already have
    -- produced this direct finite budget.
    badTailVorticityEstimate : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      (TailGood shell u → ⊥) →
      _≤_ A (vorticityExpenditure u) (tailFailureBudget shell u)

    badTailBudgetFinite : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      (TailGood shell u → ⊥) →
      BudgetFinite (tailFailureBudget shell u)

    -- Excessive size: direct continuation or a contradiction with the other
    -- admissibility conditions must produce this finite budget.
    excessiveSizeVorticityEstimate : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      TailGood shell u →
      (SizeGood shell u → ⊥) →
      _≤_ A (vorticityExpenditure u) (sizeFailureBudget shell u)

    excessiveSizeBudgetFinite : ∀ shell u →
      LargePacket shell u →
      GammaGood shell u →
      TailGood shell u →
      (SizeGood shell u → ⊥) →
      BudgetFinite (sizeFailureBudget shell u)

open PeriodicChartFailureAnalyticInputs public

gammaFailureGivesDirectBKM :
  ∀ {i} {A : AbsorptionArithmetic} {State Shell : Set i} →
  (I : PeriodicChartFailureAnalyticInputs A State Shell) →
  ∀ shell u →
  LargePacket I shell u →
  (GammaGood I shell u → ⊥) →
  DirectBKMControlled I u
gammaFailureGivesDirectBKM I shell u large failed =
  finiteVorticityImpliesDirectBKM I u
    (boundedByFiniteBudgetImpliesVorticityFinite I u
      (gammaFailureBudget I shell u)
      (badGammaVorticityEstimate I shell u large failed)
      (badGammaBudgetFinite I shell u large failed))

tailFailureGivesDirectBKM :
  ∀ {i} {A : AbsorptionArithmetic} {State Shell : Set i} →
  (I : PeriodicChartFailureAnalyticInputs A State Shell) →
  ∀ shell u →
  LargePacket I shell u →
  GammaGood I shell u →
  (TailGood I shell u → ⊥) →
  DirectBKMControlled I u
tailFailureGivesDirectBKM I shell u large gamma failed =
  finiteVorticityImpliesDirectBKM I u
    (boundedByFiniteBudgetImpliesVorticityFinite I u
      (tailFailureBudget I shell u)
      (badTailVorticityEstimate I shell u large gamma failed)
      (badTailBudgetFinite I shell u large gamma failed))

sizeFailureGivesDirectBKM :
  ∀ {i} {A : AbsorptionArithmetic} {State Shell : Set i} →
  (I : PeriodicChartFailureAnalyticInputs A State Shell) →
  ∀ shell u →
  LargePacket I shell u →
  GammaGood I shell u →
  TailGood I shell u →
  (SizeGood I shell u → ⊥) →
  DirectBKMControlled I u
sizeFailureGivesDirectBKM I shell u large gamma tail failed =
  finiteVorticityImpliesDirectBKM I u
    (boundedByFiniteBudgetImpliesVorticityFinite I u
      (sizeFailureBudget I shell u)
      (excessiveSizeVorticityEstimate I shell u large gamma tail failed)
      (excessiveSizeBudgetFinite I shell u large gamma tail failed))

analyticFailureRoutesToCoverageInputs :
  ∀ {i} {A : AbsorptionArithmetic} {State Shell : Set i} →
  PeriodicChartFailureAnalyticInputs A State Shell →
  Coverage.PeriodicChartFailureCoverageInputs State Shell
analyticFailureRoutesToCoverageInputs I = record
  { LargePacket = LargePacket I
  ; GammaGood = GammaGood I
  ; TailGood = TailGood I
  ; SizeGood = SizeGood I
  ; ChartAdmissible = ChartAdmissible I
  ; DirectBKMControlled = DirectBKMControlled I
  ; gammaDecision = gammaDecision I
  ; tailDecision = tailDecision I
  ; sizeDecision = sizeDecision I
  ; chartFromAllConditions = chartFromAllConditions I
  ; gammaFailureGivesDirectBKM = gammaFailureGivesDirectBKM I
  ; tailFailureGivesDirectBKM = tailFailureGivesDirectBKM I
  ; sizeFailureGivesDirectBKM = sizeFailureGivesDirectBKM I
  }

largePacketGivesChartOrAnalyticBKM :
  ∀ {i} {A : AbsorptionArithmetic} {State Shell : Set i} →
  (I : PeriodicChartFailureAnalyticInputs A State Shell) →
  ∀ shell u →
  LargePacket I shell u →
  ChartAdmissible I shell u ⊎ DirectBKMControlled I u
largePacketGivesChartOrAnalyticBKM I =
  Coverage.largePacketGivesChartOrDirectBKM
    (analyticFailureRoutesToCoverageInputs I)

------------------------------------------------------------------------
-- Status: all three failed-chart branches are tied to explicit finite vorticity
-- budgets.  The remaining analytic leaves are the bad-Gamma angular estimate,
-- the bad-tail secondary-chart/diffuse estimate, and the excessive-size estimate.
------------------------------------------------------------------------

chartFailureAnalyticRoutesLevel : ProofLevel
chartFailureAnalyticRoutesLevel = machineChecked

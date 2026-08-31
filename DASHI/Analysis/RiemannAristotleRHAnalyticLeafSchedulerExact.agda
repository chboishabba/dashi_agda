module DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RECURSIVE RH ANALYTIC LEAF SCHEDULER
--
-- Parent routes:
--   direct finite pole-near evaluation
--   literal target-centred explicit-formula bridge
--
-- have now been refined one level further.  The exact live leaves are:
--
--   L1 direct: construct a target-relative phase statistic and prove control;
--   L2 explicit formula: construct/admit f_{t,J} via target modulation/window
--      and prove exact spectral identification;
--   L3 Gamma: repair the deterministic Gamma evaluation to the final window.
------------------------------------------------------------------------

data RHAnalyticLeaf : Set where
  constructPoleNearPhaseStatistic
  constructPoleNearTargetWindow
  repairGammaPrecision
  sharpenZeroCount
  sharpenAbsoluteEnvelope
  reuseGenericExplicitFormulaWithoutWindow
  reuseNameOnlyHardyDonor
  : RHAnalyticLeaf

data RHLeafProducer : Set where
  finiteNearEvaluationProducer
  gammaPrecisionProducer
  : RHLeafProducer

leafFeeds : RHAnalyticLeaf → RHLeafProducer
leafFeeds constructPoleNearPhaseStatistic = finiteNearEvaluationProducer
leafFeeds constructPoleNearTargetWindow = finiteNearEvaluationProducer
leafFeeds repairGammaPrecision = gammaPrecisionProducer
leafFeeds sharpenZeroCount = finiteNearEvaluationProducer
leafFeeds sharpenAbsoluteEnvelope = finiteNearEvaluationProducer
leafFeeds reuseGenericExplicitFormulaWithoutWindow = finiteNearEvaluationProducer
leafFeeds reuseNameOnlyHardyDonor = finiteNearEvaluationProducer

data RHAnalyticLeafSchedulable : RHAnalyticLeaf → Set where
  phaseStatisticLeafLive :
    RHAnalyticLeafSchedulable constructPoleNearPhaseStatistic
  targetWindowLeafLive :
    RHAnalyticLeafSchedulable constructPoleNearTargetWindow
  gammaPrecisionLeafLive :
    RHAnalyticLeafSchedulable repairGammaPrecision

zeroCountLeafPruned : RHAnalyticLeafSchedulable sharpenZeroCount → ⊥
zeroCountLeafPruned ()

absoluteEnvelopeLeafPruned : RHAnalyticLeafSchedulable sharpenAbsoluteEnvelope → ⊥
absoluteEnvelopeLeafPruned ()

genericFormulaWithoutWindowPruned :
  RHAnalyticLeafSchedulable reuseGenericExplicitFormulaWithoutWindow → ⊥
genericFormulaWithoutWindowPruned ()

nameOnlyHardyLeafPruned :
  RHAnalyticLeafSchedulable reuseNameOnlyHardyDonor → ⊥
nameOnlyHardyLeafPruned ()

record RHAnalyticLeafCostSurface : Set₁ where
  constructor rh-analytic-leaf-cost-surface
  field
    cost : RHAnalyticLeaf → Nat
    Declared : RHAnalyticLeaf → Set
    costReference : String

open RHAnalyticLeafCostSurface public

record SelectedRHAnalyticLeaf (surface : RHAnalyticLeafCostSurface) : Set₁ where
  constructor selected-rh-analytic-leaf
  field
    selected : RHAnalyticLeaf
    selectedDeclared : Declared surface selected
    selectedSchedulable : RHAnalyticLeafSchedulable selected
    minimalAmongDeclaredLive :
      (alternative : RHAnalyticLeaf) →
      Declared surface alternative →
      RHAnalyticLeafSchedulable alternative →
      cost surface selected ≤ cost surface alternative
    selectionReference : String

open SelectedRHAnalyticLeaf public

record RHAnalyticLeafSchedulerBoundary : Set where
  constructor rh-analytic-leaf-scheduler-boundary
  field
    phaseStatisticLeafActive : Bool
    phaseStatisticLeafActiveIsTrue : phaseStatisticLeafActive ≡ true

    targetWindowLeafActive : Bool
    targetWindowLeafActiveIsTrue : targetWindowLeafActive ≡ true

    gammaPrecisionLeafActive : Bool
    gammaPrecisionLeafActiveIsTrue : gammaPrecisionLeafActive ≡ true

    countOnlyLeafActive : Bool
    countOnlyLeafActiveIsFalse : countOnlyLeafActive ≡ false

    absoluteEnvelopeLeafActive : Bool
    absoluteEnvelopeLeafActiveIsFalse : absoluteEnvelopeLeafActive ≡ false

    genericExplicitFormulaWithoutWindowActive : Bool
    genericExplicitFormulaWithoutWindowActiveIsFalse :
      genericExplicitFormulaWithoutWindowActive ≡ false

    nameOnlyHardyLeafActive : Bool
    nameOnlyHardyLeafActiveIsFalse : nameOnlyHardyLeafActive ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRHAnalyticLeafSchedulerBoundary : RHAnalyticLeafSchedulerBoundary
canonicalRHAnalyticLeafSchedulerBoundary =
  rh-analytic-leaf-scheduler-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

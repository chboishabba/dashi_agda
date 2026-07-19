module DASHI.Physics.Closure.NSSelectedCurrencyDiagnosticHarnessReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set)

import DASHI.Physics.Closure.NSCoherenceBudgetResidenceReduction as Residence
import DASHI.Physics.Closure.NSDepletionCurrencyFork as Currency

data DiagnosticOutcome : Set where
  bridgePass bridgeFails persistenceFails sourceFails budgetFails inconclusive : DiagnosticOutcome

record SelectedCurrencyDiagnosticRow
    (A : Residence.OrderedBudgetArithmetic) : Set₁ where
  field
    shell time : Residence.Scalar A
    physicalShellStretching dissipationShell normalizedStretching : Residence.Scalar A
    currencies : Currency.DepletionCurrencyFamily A
    selectedCurrency : Currency.DepletionCurrencyBranch
    concentrationPenalty adjustedBridgeConstant : Residence.Scalar A
    positivePersistence positiveSource weightedPositiveSource : Residence.Scalar A
    highShellBudget : Residence.Scalar A
    rowOutcome : DiagnosticOutcome

open SelectedCurrencyDiagnosticRow public

record SelectedCurrencyDiagnosticHarness
    (A : Residence.OrderedBudgetArithmetic) : Set₁ where
  field
    row : SelectedCurrencyDiagnosticRow A
    selectedCurrencyControlsPhysicalStretching : Set
    positivePersistenceSubcritical : Set
    positiveSourceWeightedSummable : Set
    highShellBudgetBeatsHalfDerivative : Set
    coherentTubeReplenishmentExcluded : Set

    physicalBridgeProved actualNSDynamicDecayProved
      stretchAbsorptionProved clayNavierStokesPromoted : Bool

    physicalBridgeProvedIsFalse : physicalBridgeProved ≡ false
    actualNSDynamicDecayProvedIsFalse : actualNSDynamicDecayProved ≡ false
    stretchAbsorptionProvedIsFalse : stretchAbsorptionProved ≡ false
    clayNavierStokesPromotedIsFalse : clayNavierStokesPromoted ≡ false

open SelectedCurrencyDiagnosticHarness public

selectedCurrencyHarnessForcesResidenceBound :
  (A : Residence.OrderedBudgetArithmetic) →
  (I : Currency.SelectedCurrencyResidenceInputs A) →
  Residence._≤_ A
    (Residence._*_ A
      (Residence._*_ A
        (Currency.absorptionMargin I)
        (Currency.dangerCost I))
      (Currency.dangerousResidence I))
    (Currency.budgetUpper I)
selectedCurrencyHarnessForcesResidenceBound A I =
  Currency.selectedDepletionCurrencyForcesResidenceBound A I

record NSSelectedCurrencyDiagnosticHarnessReceipt : Set₁ where
  field
    originalSelfAdvectiveCandidateFalsified : Bool
    replacementCurrencyForkActive : Bool

    directionTurnoverCandidateOpen : Bool
    spectralProjectorTurnoverCandidateOpen : Bool
    crossShellCoherenceCandidateOpen : Bool
    middleSimpleSpectrumCandidateOpen : Bool

    selectedCurrencyDiagnosticHarnessDefined : Bool
    nextRequiredTableColumns : Set

    physicalBridgeStillOpen : Bool
    actualFlowDecayStillOpen : Bool
    coherentTubeExclusionStillOpen : Bool
    clayNavierStokesPromoted : Bool

    physicalBridgeStillOpenIsTrue : physicalBridgeStillOpen ≡ true
    actualFlowDecayStillOpenIsTrue : actualFlowDecayStillOpen ≡ true
    coherentTubeExclusionStillOpenIsTrue : coherentTubeExclusionStillOpen ≡ true
    clayNavierStokesPromotedIsFalse : clayNavierStokesPromoted ≡ false

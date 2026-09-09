module DASHI.GameTheory.SequentialGameFractranWolframCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.SequentialExtensiveFormExact as Sequential
import DASHI.Combinatorics.FractranComputationEquivalence as Fractran
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural
import DASHI.Biology.AgenticLevinWolframResidualCrossPollinationExact as WolframAgentic

------------------------------------------------------------------------
-- SEQUENTIAL GAME / FRACTRAN / WOLFRAM CROSS-POLLINATION
--
-- A fixed strategy profile may induce an executable history machine.  FRACTRAN
-- is used only when the existing representation owner supplies halt, step and
-- run preservation.  Separately, a Wolfram-style visible endpoint may quotient
-- several histories while a residual remains relevant to the next strategic
-- continuation.  Same endpoint, same terminal payoff and same implementation
-- are intentionally distinct claims.
------------------------------------------------------------------------

record StrategyInducedHistoryMachine
    (G : Sequential.ExtensiveStrategicGame) : Set₁ where
  constructor strategy-induced-history-machine
  field
    plans : Sequential.PlanProfile G

    stepHistory :
      Sequential.History G →
      Maybe (Sequential.History G)

    runHistory :
      Sequential.History G →
      Sequential.History G

    TerminalHistory : Sequential.History G → Set

    haltExactlyAtTerminal :
      (history : Sequential.History G) →
      TerminalHistory history →
      stepHistory history ≡ nothing

    runEndsTerminal :
      (history : Sequential.History G) →
      TerminalHistory (runHistory history)

    executionReference : String

open StrategyInducedHistoryMachine public

asFractranSourceMachine :
  ∀ {G} →
  StrategyInducedHistoryMachine G →
  Fractran.SourceMachine
asFractranSourceMachine {G} machine = record
  { State = Sequential.History G
  ; sourceStep = stepHistory machine
  ; sourceRun = runHistory machine
  }

record SequentialFractranRepresentation
    {G : Sequential.ExtensiveStrategicGame}
    (machine : StrategyInducedHistoryMachine G) : Set₁ where
  constructor sequential-fractran-representation
  field
    representation :
      Fractran.FractranRepresentation
        (asFractranSourceMachine machine)

    strategyMachineReference : String
    fractranRepresentationReference : String

open SequentialFractranRepresentation public

fractranPreservesSameStrategyRunOutcome :
  ∀ {G machine}
    (R : SequentialFractranRepresentation {G} machine) →
  {left right : Sequential.History G} →
  runHistory machine left ≡ runHistory machine right →
  Fractran.SameOutcome
    (Fractran.encode (representation R) left)
    (Fractran.encode (representation R) right)
fractranPreservesSameStrategyRunOutcome R same =
  Fractran.representation-preserves-same-outcome
    (representation R)
    same

------------------------------------------------------------------------
-- Consumer-relative Wolfram-style history fibre.
------------------------------------------------------------------------

record StrategicHistoryFibre
    (G : Sequential.ExtensiveStrategicGame) : Set₁ where
  constructor strategic-history-fibre
  field
    Visible Residual : Set

    visible : Sequential.History G → Visible
    residual : Sequential.History G → Residual

    continuationPlan :
      Residual → Sequential.PlanProfile G

    observationReference : String
    residualReference : String
    continuationReference : String

open StrategicHistoryFibre public

record SameVisibleDifferentStrategicContinuation
    {G : Sequential.ExtensiveStrategicGame}
    (F : StrategicHistoryFibre G) : Set₁ where
  constructor same-visible-different-strategic-continuation
  field
    leftHistory rightHistory : Sequential.History G

    sameVisible :
      visible F leftHistory ≡ visible F rightHistory

    ResidualDifferent : Residual F → Residual F → Set
    residualsDiffer :
      ResidualDifferent
        (residual F leftHistory)
        (residual F rightHistory)

    ContinuationDifferent :
      Sequential.PlanProfile G →
      Sequential.PlanProfile G → Set

    continuationsDiffer :
      ContinuationDifferent
        (continuationPlan F (residual F leftHistory))
        (continuationPlan F (residual F rightHistory))

    collisionReference : String

open SameVisibleDifferentStrategicContinuation public

------------------------------------------------------------------------
-- Existing concrete multiway fixture reused as a compatibility witness.
------------------------------------------------------------------------

naturalVisibleEndpointCollision :
  Natural.visibleEndpoint (Natural.executeMultiway Natural.leftThenRight)
  ≡ Natural.visibleEndpoint (Natural.executeMultiway Natural.rightThenLeft)
naturalVisibleEndpointCollision = Natural.multiwayPathsShareVisibleEndpoint

naturalLeftResidual :
  Natural.pathResidual (Natural.executeMultiway Natural.leftThenRight) ≡ 1
naturalLeftResidual = refl

naturalRightResidual :
  Natural.pathResidual (Natural.executeMultiway Natural.rightThenLeft) ≡ 2
naturalRightResidual = refl

wolframAgenticBoundary :
  WolframAgentic.AgenticLevinWolframCrossPollinationBoundary
wolframAgenticBoundary =
  WolframAgentic.canonicalAgenticLevinWolframCrossPollinationBoundary

fractranUniversalityBoundary : Fractran.FractranUniversalityBoundary
fractranUniversalityBoundary = Fractran.canonicalFractranUniversalityBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameTerminalPayoffMeansSameTracePermission : Set where

data SameVisibleEndpointMeansSameStrategyPermission : Set where

data FractranEncodingMeansUniversalCompilerPermission : Set where

data FractranSameOutcomeMeansSameHistoryPermission : Set where

data MultiwayBranchMeansPlayerChoicePermission : Set where

data ComputationalBranchMeansStrategicPreferencePermission : Set where

data CausalInvarianceMeansGameEquilibriumPermission : Set where

sameTerminalPayoffDoesNotRecoverTrace :
  SameTerminalPayoffMeansSameTracePermission → ⊥
sameTerminalPayoffDoesNotRecoverTrace ()

sameVisibleEndpointDoesNotRecoverStrategy :
  SameVisibleEndpointMeansSameStrategyPermission → ⊥
sameVisibleEndpointDoesNotRecoverStrategy ()

fractranRepresentationDoesNotCreateUniversalCompiler :
  FractranEncodingMeansUniversalCompilerPermission → ⊥
fractranRepresentationDoesNotCreateUniversalCompiler ()

fractranSameOutcomeDoesNotRecoverHistory :
  FractranSameOutcomeMeansSameHistoryPermission → ⊥
fractranSameOutcomeDoesNotRecoverHistory ()

multiwayBranchDoesNotAutomaticallyMeanPlayerChoice :
  MultiwayBranchMeansPlayerChoicePermission → ⊥
multiwayBranchDoesNotAutomaticallyMeanPlayerChoice ()

computationalBranchDoesNotCreatePreference :
  ComputationalBranchMeansStrategicPreferencePermission → ⊥
computationalBranchDoesNotCreatePreference ()

causalInvarianceDoesNotCreateEquilibrium :
  CausalInvarianceMeansGameEquilibriumPermission → ⊥
causalInvarianceDoesNotCreateEquilibrium ()

record SequentialGameComputationBoundary : Set where
  constructor sequential-game-computation-boundary
  field
    strategyInducedMachineExplicit : Bool
    fractranRepresentationUsesExistingReceipt : Bool
    haltStepRunPreservationRequired : Bool
    visibleEndpointAndResidualSeparated : Bool
    residualMayChangeStrategicContinuation : Bool
    sameOutcomeAutomaticallySameTrace : Bool
    multiwayBranchAutomaticallyPlayerChoice : Bool
    causalInvarianceAutomaticallyEquilibrium : Bool

canonicalSequentialGameComputationBoundary : SequentialGameComputationBoundary
canonicalSequentialGameComputationBoundary =
  sequential-game-computation-boundary
    true true true true true false false false

module DASHI.Physics.Foundations.Round5AttachedCompletionBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as HistoryInternal
import DASHI.Physics.Foundations.FiniteResidueCycleReachabilityExact as ResidueInternal
import DASHI.Physics.Foundations.FiniteMultiscaleKernelCompatibilityExact as MultiscaleInternal
import DASHI.Physics.Foundations.FiniteUltrametricReebFlowExact as Ultrametric
import DASHI.Physics.Foundations.ProbabilityDecoratedReebExact as Reeb

module History = HistoryInternal
module Residue = ResidueInternal
module Multiscale = MultiscaleInternal

record Round5AttachedCompletionBoundary : Set where
  field
    finiteHistoryFunctionalBoundary :
      History.FiniteHistoryFunctionalBoundary
    finiteResidueCycleBoundary :
      Residue.FiniteResidueCycleReachabilityBoundary
    finiteMultiscaleKernelBoundary :
      Multiscale.FiniteMultiscaleKernelCompatibilityBoundary
    finiteUltrametricReebBoundary :
      Ultrametric.FiniteUltrametricReebFlowBoundary

    reversibleSubsystemWitness :
      (configuration : History.Configuration) →
      History.reversibleStep (History.reversibleStep configuration)
      ≡
      configuration

    twoBoundaryPruningWitness :
      (final : History.FinalBoundary) →
      History.compatibleWithBoundaries
        History.initialA
        final
        (History.prunedHistory final)
      ≡
      History.compatible

    residueSixCycleWitness :
      (residue : Residue.Residue6) →
      Residue.successor6Six residue ≡ residue

    residueNineCycleWitness :
      (residue : Residue.Residue9) →
      Residue.successor9Nine residue ≡ residue

    boundedReachabilityWitness :
      Residue.reachStepTwo Residue.reachStart ≡ Residue.reachTerminal

    exactMultiscaleCompatibilityWitness :
      (state : Multiscale.FineState) →
      Multiscale.coarseProjection (Multiscale.fineKernelExact state)
      ≡
      Multiscale.coarseKernelExact (Multiscale.coarseProjection state)

    nonzeroCompatibilityDefectWitness :
      Multiscale.compatibilityDefect Multiscale.fineLeftLow ≡ 1

    splitTransitionNormalisationWitness :
      Ultrametric.transitionWeight Reeb.sourceToLeft
      +
      Ultrametric.transitionWeight Reeb.sourceToRight
      ≡
      6

    finiteHistoryWeightWitness :
      Ultrametric.historyWeight Ultrametric.rightHistory ≡ 24

open Round5AttachedCompletionBoundary public

canonicalRound5AttachedCompletionBoundary :
  Round5AttachedCompletionBoundary
canonicalRound5AttachedCompletionBoundary =
  record
    { finiteHistoryFunctionalBoundary =
        History.canonicalFiniteHistoryFunctionalBoundary
    ; finiteResidueCycleBoundary =
        Residue.canonicalFiniteResidueCycleReachabilityBoundary
    ; finiteMultiscaleKernelBoundary =
        Multiscale.canonicalFiniteMultiscaleKernelCompatibilityBoundary
    ; finiteUltrametricReebBoundary =
        Ultrametric.canonicalFiniteUltrametricReebFlowBoundary
    ; reversibleSubsystemWitness =
        History.reversibleStepInvolutive
    ; twoBoundaryPruningWitness =
        History.pruningSelectsCompatibleHistory
    ; residueSixCycleWitness =
        Residue.sixCycleReturns
    ; residueNineCycleWitness =
        Residue.nineCycleReturns
    ; boundedReachabilityWitness =
        Residue.terminalReachableWithinTwo
    ; exactMultiscaleCompatibilityWitness =
        Multiscale.exactKernelCompatibility
    ; nonzeroCompatibilityDefectWitness =
        Multiscale.canonicalDefectIsOne
    ; splitTransitionNormalisationWitness =
        Ultrametric.splitRowNormalisesToSix
    ; finiteHistoryWeightWitness =
        Ultrametric.rightHistoryWeightIsTwentyFour
    }

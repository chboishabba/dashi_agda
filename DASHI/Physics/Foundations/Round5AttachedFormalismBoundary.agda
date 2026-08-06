module DASHI.Physics.Foundations.Round5AttachedFormalismBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as HistoryInternal
import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as Weight
import DASHI.Physics.Foundations.FormalReceiptBoundaryExact as Receipt
import DASHI.Physics.Foundations.FiniteWeightedTernaryKernelExact as WeightedKernel
import DASHI.Physics.Foundations.TernaryKernelQuotientLyapunovExact as KernelInternal
import DASHI.Physics.Foundations.FiniteStatisticalFiltrationExact as Statistics
import DASHI.Physics.Foundations.ProbabilityDecoratedReebExact as Reeb
import DASHI.Physics.Foundations.AttachedFormalismSourceAtlas as Sources
import DASHI.Biology.TriadicKernelLiftQuotientExact as TriadicInternal

module History = HistoryInternal
module Kernel = KernelInternal
module Triadic = TriadicInternal

record Round5AttachedFormalismBoundary : Set where
  field
    historyOrientationBoundary : History.FiniteHistoryOrientationBoundary
    historyWeightFiltrationBoundary : Weight.HistoryWeightFiltrationBoundary
    formalReceiptBoundary : Receipt.FormalReceiptBoundary
    weightedTernaryKernelBoundary :
      WeightedKernel.FiniteWeightedTernaryKernelBoundary
    ternaryKernelBoundary : Kernel.TernaryKernelQuotientLyapunovBoundary
    statisticalFiltrationBoundary :
      Statistics.FiniteStatisticalFiltrationBoundary
    probabilityReebBoundary : Reeb.ProbabilityDecoratedReebBoundary

    historyReversalIsInvolutive :
      (h : History.History2) →
      History.reverseHistory (History.reverseHistory h) ≡ h

    actionIsTimeReversalInvariant :
      (h : History.History2) →
      History.historyAction (History.reverseHistory h)
      ≡
      History.historyAction h

    noBackwardSignalInCanonicalTable :
      History.pastAccessibleOutcome History.chooseMinusBoundary
      ≡
      History.pastAccessibleOutcome History.choosePlusBoundary

    terminalObserverSeesTerminalEvent :
      Weight.visibleAt Weight.terminalFiltration Weight.terminalEvent ≡ true

    stageCycleHasPeriodFour :
      (stage : Receipt.TlureyStage) →
      Receipt.nextStageFour stage ≡ stage

    symmetricKernelCommutesWithSwap :
      (sheet : Triadic.NineSheet) →
      WeightedKernel.symmetricKernel (WeightedKernel.swapCoordinates sheet)
      ≡
      WeightedKernel.swapCoordinates
        (WeightedKernel.symmetricKernel sheet)

    quotientKernelDescends :
      (sheet : Triadic.NineSheet) →
      Triadic.quotientNine (Kernel.sheetKernel sheet)
      ≡
      Kernel.quotientKernel (Triadic.quotientNine sheet)

    quotientKernelConvergesInTwo :
      (orbit : Triadic.NineOrbit) →
      Kernel.quotientKernel (Kernel.quotientKernel orbit)
      ≡
      Triadic.zeroOrbit

    coarseStatisticalProjectionIsNonInjective :
      Statistics.coarseProjection Statistics.fineLeftLow
      ≡
      Statistics.coarseProjection Statistics.fineLeftHigh

    reebSplitConservesMass :
      Reeb.massBefore Reeb.sourceComponent
      ≡
      Reeb.massSplit Reeb.leftComponent
      +
      Reeb.massSplit Reeb.rightComponent

    reebMergePreservesBothFeatures :
      (component : Reeb.IncomingComponent) →
      Reeb.embedIntoMerge component ≡ Reeb.incomingFeature component

    attachedSourceCountIsSix :
      Sources.canonicalAttachedFormalismSourceCount ≡ 6

open Round5AttachedFormalismBoundary public

canonicalRound5AttachedFormalismBoundary :
  Round5AttachedFormalismBoundary
canonicalRound5AttachedFormalismBoundary =
  record
    { historyOrientationBoundary =
        History.canonicalFiniteHistoryOrientationBoundary
    ; historyWeightFiltrationBoundary =
        Weight.canonicalHistoryWeightFiltrationBoundary
    ; formalReceiptBoundary =
        Receipt.canonicalFormalReceiptBoundary
    ; weightedTernaryKernelBoundary =
        WeightedKernel.canonicalFiniteWeightedTernaryKernelBoundary
    ; ternaryKernelBoundary =
        Kernel.canonicalTernaryKernelQuotientLyapunovBoundary
    ; statisticalFiltrationBoundary =
        Statistics.canonicalFiniteStatisticalFiltrationBoundary
    ; probabilityReebBoundary =
        Reeb.canonicalProbabilityDecoratedReebBoundary
    ; historyReversalIsInvolutive =
        History.reverseHistoryInvolutive
    ; actionIsTimeReversalInvariant =
        History.actionTimeReversalInvariant
    ; noBackwardSignalInCanonicalTable =
        History.finiteNoBackwardSignalling
    ; terminalObserverSeesTerminalEvent =
        refl
    ; stageCycleHasPeriodFour =
        Receipt.fourCycleReturns
    ; symmetricKernelCommutesWithSwap =
        WeightedKernel.symmetricKernelCommutesWithCoordinateSwap
    ; quotientKernelDescends =
        Kernel.sheetKernelDescends
    ; quotientKernelConvergesInTwo =
        Kernel.quotientKernelReachesFixedClassInTwo
    ; coarseStatisticalProjectionIsNonInjective =
        Statistics.coarseProjectionIsNonInjective
    ; reebSplitConservesMass =
        Reeb.splitConservesMass
    ; reebMergePreservesBothFeatures =
        Reeb.mergePreservesIncomingFeature
    ; attachedSourceCountIsSix =
        Sources.canonicalAttachedFormalismSourceCountIsSix
    }

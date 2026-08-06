module DASHI.Physics.Foundations.Round5AttachedFormalismBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as History
import DASHI.Physics.Foundations.FormalReceiptBoundaryExact as Receipt
import DASHI.Physics.Foundations.TernaryKernelQuotientLyapunovExact as Kernel
import DASHI.Physics.Foundations.ProbabilityDecoratedReebExact as Reeb
import DASHI.Physics.Foundations.AttachedFormalismSourceAtlas as Sources
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

record Round5AttachedFormalismBoundary : Set where
  field
    historyOrientationBoundary : History.FiniteHistoryOrientationBoundary
    formalReceiptBoundary : Receipt.FormalReceiptBoundary
    ternaryKernelBoundary : Kernel.TernaryKernelQuotientLyapunovBoundary
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

    stageCycleHasPeriodFour :
      (stage : Receipt.TlureyStage) →
      Receipt.nextStageFour stage ≡ stage

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
    ; formalReceiptBoundary =
        Receipt.canonicalFormalReceiptBoundary
    ; ternaryKernelBoundary =
        Kernel.canonicalTernaryKernelQuotientLyapunovBoundary
    ; probabilityReebBoundary =
        Reeb.canonicalProbabilityDecoratedReebBoundary
    ; historyReversalIsInvolutive =
        History.reverseHistoryInvolutive
    ; actionIsTimeReversalInvariant =
        History.actionTimeReversalInvariant
    ; noBackwardSignalInCanonicalTable =
        History.finiteNoBackwardSignalling
    ; stageCycleHasPeriodFour =
        Receipt.fourCycleReturns
    ; quotientKernelDescends =
        Kernel.sheetKernelDescends
    ; quotientKernelConvergesInTwo =
        Kernel.quotientKernelReachesFixedClassInTwo
    ; reebSplitConservesMass =
        Reeb.splitConservesMass
    ; reebMergePreservesBothFeatures =
        Reeb.mergePreservesIncomingFeature
    ; attachedSourceCountIsSix =
        Sources.canonicalAttachedFormalismSourceCountIsSix
    }

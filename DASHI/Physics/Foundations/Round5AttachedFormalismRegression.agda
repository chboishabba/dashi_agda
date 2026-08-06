module DASHI.Physics.Foundations.Round5AttachedFormalismRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as History
import DASHI.Physics.Foundations.HistoryWeightFiltrationExact as Weight
import DASHI.Physics.Foundations.FormalReceiptBoundaryExact as Receipt
import DASHI.Physics.Foundations.FiniteWeightedTernaryKernelExact as WeightedKernel
import DASHI.Physics.Foundations.TernaryKernelQuotientLyapunovExact as Kernel
import DASHI.Physics.Foundations.FiniteStatisticalFiltrationExact as Statistics
import DASHI.Physics.Foundations.ProbabilityDecoratedReebExact as Reeb
import DASHI.Physics.Foundations.AttachedFormalismSourceAtlas as Sources
import DASHI.Physics.Foundations.Round5AttachedFormalismBoundary as Boundary
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

attachedBoundaryExists : Boundary.Round5AttachedFormalismBoundary
attachedBoundaryExists = Boundary.canonicalRound5AttachedFormalismBoundary

historyRegression :
  History.reverseHistory
    (History.reverseHistory (History.stateMinus , History.statePlus))
  ≡
  (History.stateMinus , History.statePlus)
historyRegression = refl

historyActionRegression :
  History.historyAction
    (History.reverseHistory (History.stateMinus , History.statePlus))
  ≡
  History.historyAction (History.stateMinus , History.statePlus)
historyActionRegression = refl

noSignalRegression :
  History.pastAccessibleOutcome History.chooseMinusBoundary
  ≡
  History.pastAccessibleOutcome History.choosePlusBoundary
noSignalRegression = History.finiteNoBackwardSignalling

weightSeparationRegression :
  Weight.visibleAt Weight.initialFiltration Weight.terminalEvent ≡ false
  ×
  Weight.visibleAt Weight.terminalFiltration Weight.terminalEvent ≡ true
weightSeparationRegression = refl , refl

arrowFunctionalRegression :
  Weight.entropyValue Weight.arrowFinal
  ≡
  Weight.entropyValue Weight.arrowInitial + 1
  ×
  Weight.descriptionLengthValue Weight.arrowFinal
  ≡
  Weight.descriptionLengthValue Weight.arrowInitial + 2
arrowFunctionalRegression = refl , refl

receiptSeparationRegression :
  Receipt.sourceOnlyReceipt ≡ Receipt.kernelReceipt → ⊥
receiptSeparationRegression = Receipt.sourceOnlyIsNotKernelReceipt

cycleRegression :
  Receipt.nextStageFour Receipt.overflowStage ≡ Receipt.overflowStage
cycleRegression = refl

thresholdRegression :
  Receipt.classifyThreshold Receipt.aboveThresholdLevel
  ≡
  Receipt.ascendedState
thresholdRegression = refl

weightedEquivarianceRegression :
  WeightedKernel.symmetricKernel
    (WeightedKernel.swapCoordinates
      (Triadic.negativeTrit , Triadic.positiveTrit))
  ≡
  WeightedKernel.swapCoordinates
    (WeightedKernel.symmetricKernel
      (Triadic.negativeTrit , Triadic.positiveTrit))
weightedEquivarianceRegression = refl

asymmetricWeightCounterexampleRegression :
  WeightedKernel.asymmetricKernel
    (WeightedKernel.swapCoordinates WeightedKernel.asymmetricWitness)
  ≡
  WeightedKernel.swapCoordinates
    (WeightedKernel.asymmetricKernel WeightedKernel.asymmetricWitness)
  →
  ⊥
asymmetricWeightCounterexampleRegression =
  WeightedKernel.asymmetricKernelBreaksCoordinateSwap

quotientDescentRegression :
  Triadic.quotientNine
    (Kernel.sheetKernel
      (Triadic.positiveTrit , Triadic.negativeTrit))
  ≡
  Kernel.quotientKernel
    (Triadic.quotientNine
      (Triadic.positiveTrit , Triadic.negativeTrit))
quotientDescentRegression =
  Kernel.sheetKernelDescends
    (Triadic.positiveTrit , Triadic.negativeTrit)

periodicCounterexampleRegression :
  Kernel.oscillatingKernel
    (Kernel.oscillatingKernel Triadic.firstAxisOrbit)
  ≡
  Triadic.firstAxisOrbit
periodicCounterexampleRegression = refl

lyapunovConvergenceRegression :
  Kernel.quotientKernel
    (Kernel.quotientKernel Triadic.oppositeSignOrbit)
  ≡
  Triadic.zeroOrbit
lyapunovConvergenceRegression = refl

statisticalCarrierSeparationRegression :
  Statistics.physicalObject Statistics.physicalLeft
  ≡
  Statistics.lawObject Statistics.balancedLaw
  →
  ⊥
statisticalCarrierSeparationRegression =
  Statistics.physicalObjectCannotEqualLawObject
    Statistics.physicalLeft
    Statistics.balancedLaw

statisticalDistanceRegression :
  Statistics.parameterDistance Statistics.parameterLeft Statistics.parameterRight
  ≡
  Statistics.parameterDistance Statistics.parameterRight Statistics.parameterLeft
statisticalDistanceRegression = refl

coarseProjectionRegression :
  Statistics.coarseProjection Statistics.fineLeftLow
  ≡
  Statistics.coarseProjection Statistics.fineLeftHigh
coarseProjectionRegression = Statistics.coarseProjectionIsNonInjective

persistenceRegression :
  Statistics.persistentFeature Statistics.scaleOne
  ≡
  Statistics.featurePresent
  ×
  Statistics.persistentFeature Statistics.scaleThree
  ≡
  Statistics.featureAbsent
persistenceRegression = refl , refl

reebMassRegression :
  Reeb.massSplit Reeb.leftComponent
  +
  Reeb.massSplit Reeb.rightComponent
  ≡
  Reeb.massMerged Reeb.mergedComponent
reebMassRegression = refl

reebSemanticsRegression :
  Reeb.CompatibleTransition
    (Reeb.nodeLabel (Reeb.edgeSource Reeb.rightToMerge))
    (Reeb.nodeLabel (Reeb.edgeTarget Reeb.rightToMerge))
reebSemanticsRegression =
  Reeb.canonicalEdgeIsSemanticallyCompatible Reeb.rightToMerge

mdlRegression :
  Reeb.totalDescriptionLength Reeb.selectedReebModel ≡ 7
mdlRegression = refl

sourceRegression : Sources.canonicalAttachedFormalismSourceCount ≡ 6
sourceRegression = Sources.canonicalAttachedFormalismSourceCountIsSix

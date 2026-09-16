module DASHI.ComputerScience.RSA260BidiProjectionFreezeObservableValidationExact where

import DASHI.ComputerScience.RSA260BidiProjectionFreezeObservableExact as Freeze

freezeReceipt : Freeze.ProjectionPairFreezeReceipt
freezeReceipt = Freeze.currentProjectionPairFreezeReceipt

baselinePacket : Freeze.ProjectionIndexedObservable
baselinePacket = Freeze.carrier32BaselineObservable

samePairCrossCarrierComparison :
  Freeze.CrossCarrierComparisonAdmissible
    Freeze.carrier32BaselineObservable
    Freeze.carrier128BaselineObservable
samePairCrossCarrierComparison = Freeze.baselineCrossCarrierComparison

mismatchedProjectionPairRejected :
  Freeze.CrossCarrierComparisonAdmissible
    Freeze.carrier128BaselineObservable
    Freeze.carrier128Y1Observable → Freeze.⊥
mismatchedProjectionPairRejected = Freeze.mismatchedProjectionPairNotComparable

freezeBoundary : Freeze.ProjectionFreezeInterpretationBoundary
freezeBoundary = Freeze.canonicalProjectionFreezeInterpretationBoundary

nextResidual : Freeze.ProjectionFreezeResidual
nextResidual = Freeze.firstProjectionFreezeResidual

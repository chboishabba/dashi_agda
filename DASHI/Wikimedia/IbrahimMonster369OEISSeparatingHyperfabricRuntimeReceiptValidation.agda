module DASHI.Wikimedia.IbrahimMonster369OEISSeparatingHyperfabricRuntimeReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonster369OEISSeparatingHyperfabricRuntimeReceiptExact as R

receipt : R.Monster369RuntimeReceipt
receipt = R.currentMonster369RuntimeReceipt

coordinateCountRegression : R.coordinateCount receipt ≡ 24
coordinateCountRegression = refl

edgeCountRegression : R.edgeCount receipt ≡ 5
edgeCountRegression = refl

previousMinimumSizeRegression : R.previousRuntimeMinimumTransversalSize receipt ≡ 2
previousMinimumSizeRegression = refl

previousMinimumCountRegression : R.previousRuntimeMinimumTransversalCount receipt ≡ 1
previousMinimumCountRegression = refl

previousRuntimeObservedRegression :
  R.previousExhaustiveRuntimeSearchObserved receipt ≡ true
previousRuntimeObservedRegression = refl

currentRuntimeNotObservedRegression :
  R.exactCurrentRevisionRuntimeObserved receipt ≡ false
currentRuntimeNotObservedRegression = refl

currentDriftGuardNotObservedRegression :
  R.exactCurrentRevisionAgdaCoordinateDriftGuardObserved receipt ≡ false
currentDriftGuardNotObservedRegression = refl

c6ExpansionRegression :
  R.c6WeightTwoSpectrumCoordinateAddedAfterPreviousRuntime receipt ≡ true
c6ExpansionRegression = refl

oeisNegativeControlRegression :
  R.oeisOnlyHitsEveryDeclaredConsumer receipt ≡ false
oeisNegativeControlRegression = refl

pythonAuthorityRegression :
  R.pythonRuntimeCreatesMonsterTheorem receipt ≡ false
pythonAuthorityRegression = refl

kernelMinimumRegression :
  R.minimumHittingSetKernelProved receipt ≡ false
kernelMinimumRegression = refl

coordinateProofRegression :
  R.coordinateSelectionCreatesConsumerProof receipt ≡ false
coordinateProofRegression = refl

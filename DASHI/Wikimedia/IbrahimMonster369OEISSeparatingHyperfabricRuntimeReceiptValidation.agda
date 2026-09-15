module DASHI.Wikimedia.IbrahimMonster369OEISSeparatingHyperfabricRuntimeReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Wikimedia.IbrahimMonster369OEISSeparatingHyperfabricRuntimeReceiptExact as R

receipt : R.Monster369RuntimeReceipt
receipt = R.currentMonster369RuntimeReceipt

coordinateCountRegression : R.coordinateCount receipt ≡ 23
coordinateCountRegression = refl

edgeCountRegression : R.edgeCount receipt ≡ 5
edgeCountRegression = refl

minimumSizeRegression : R.runtimeMinimumTransversalSize receipt ≡ 2
minimumSizeRegression = refl

minimumCountRegression : R.runtimeMinimumTransversalCount receipt ≡ 1
minimumCountRegression = refl

characterCoordinateRegression :
  R.minimumContainsMonster3B65610Character receipt ≡ true
characterCoordinateRegression = refl

actionCoordinateRegression :
  R.minimumContainsActualWeylActionCoordinate receipt ≡ true
actionCoordinateRegression = refl

oeisNegativeControlRegression :
  R.oeisOnlyHitsEveryDeclaredConsumer receipt ≡ false
oeisNegativeControlRegression = refl

pythonAuthorityFirewallRegression :
  R.pythonRuntimeCreatesMonsterTheorem receipt ≡ false
pythonAuthorityFirewallRegression = refl

kernelMinimumFirewallRegression :
  R.minimumHittingSetKernelProved receipt ≡ false
kernelMinimumFirewallRegression = refl

coordinateProofFirewallRegression :
  R.coordinateSelectionCreatesConsumerProof receipt ≡ false
coordinateProofFirewallRegression = refl

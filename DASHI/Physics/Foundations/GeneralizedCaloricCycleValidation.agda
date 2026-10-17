module DASHI.Physics.Foundations.GeneralizedCaloricCycleValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Foundations.GeneralizedCaloricCycleExact as Caloric

finiteCycleExists : Caloric.FiniteCaloricCycle
finiteCycleExists = Caloric.canonicalFiniteCaloricCycle

coldHeatIsFour :
  Caloric.coldHeat Caloric.canonicalFiniteCaloricCycle ≡ 4
coldHeatIsFour = refl

hotHeatIsSeven :
  Caloric.hotHeat Caloric.canonicalFiniteCaloricCycle ≡ 7
hotHeatIsSeven = refl

workInputIsThree :
  Caloric.workInput Caloric.canonicalFiniteCaloricCycle ≡ 3
workInputIsThree = refl

firstLawClosesExactly :
  Caloric.hotHeat Caloric.canonicalFiniteCaloricCycle
    ≡
  Caloric.coldHeat Caloric.canonicalFiniteCaloricCycle
    + Caloric.workInput Caloric.canonicalFiniteCaloricCycle
firstLawClosesExactly = Caloric.firstLawReceipt Caloric.canonicalFiniteCaloricCycle

moireGeometryIsCandidateControl : Caloric.CaloricControlKind
moireGeometryIsCandidateControl = Caloric.moireGeometryCandidate

physicalGeometryCaloricRealizationUnpaid :
  Caloric.sameObjectMeasuredResponse Caloric.canonicalGeometryCaloricCandidate ≡ false
physicalGeometryCaloricRealizationUnpaid = refl

physicalUsefulCoolingUnpaid :
  Caloric.measuredUsefulColdHeat Caloric.canonicalGeometryCaloricCandidate ≡ false
physicalUsefulCoolingUnpaid = refl

finiteArithmeticDoesNotPromotePhysicalUtility : Bool
finiteArithmeticDoesNotPromotePhysicalUtility =
  Caloric.finiteFixtureDoesNotPayPhysicalCycle Caloric.canonicalGeneralizedCaloricBoundary

module DASHI.Physics.Foundations.QuantumStressEnergySourceWeldValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.QuantumStressEnergySourceWeldExact as Weld

brownMaclayStressSourceExists : Weld.ParallelPlateStressSource
brownMaclayStressSourceExists = Weld.canonicalBrownMaclayStressSource

qftStressTheoryPaid :
  Weld.qftExpectationTheoryPaid Weld.canonicalQuantumStressSourcePayment ≡ true
qftStressTheoryPaid = refl

quantumInequalityLiteraturePaid :
  Weld.quantumInequalityLiteraturePaid Weld.canonicalQuantumStressSourcePayment ≡ true
quantumInequalityLiteraturePaid = refl

sameObjectStressMeasurementStillOpen :
  Weld.sameObjectRenormalizedStressMeasured Weld.canonicalQuantumStressSourcePayment ≡ false
sameObjectStressMeasurementStillOpen = refl

macroscopicScalingStillOpen :
  Weld.macroscopicControlledScalingPaid Weld.canonicalQuantumStressSourcePayment ≡ false
macroscopicScalingStillOpen = refl

gravityBackreactionStillOpen :
  Weld.measuredGravitationalBackreactionPaid Weld.canonicalQuantumStressSourcePayment ≡ false
gravityBackreactionStillOpen = refl

casimirForceNotGravityMeasurement : Bool
casimirForceNotGravityMeasurement =
  Weld.casimirForceDoesNotMeasureGravity Weld.canonicalQuantumStressSourceBoundary

backgroundVacuumNeedsCorrectQIBaseline : Bool
backgroundVacuumNeedsCorrectQIBaseline =
  Weld.quantumInequalityMustRespectBackgroundVacuum Weld.canonicalQuantumStressSourceBoundary

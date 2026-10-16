module DASHI.Physics.QuantumVacuum.Casimir369StressEnergyTerminalMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.Casimir369StressEnergyTerminalMaxCutExact as Terminal

------------------------------------------------------------------------
-- RED-first terminal regression surface.
------------------------------------------------------------------------

finiteStructurePaidRegression :
  Terminal.finite369StructurePaid Terminal.canonicalTerminalBoundary ≡ true
finiteStructurePaidRegression = refl

localStressPaidRegression :
  Terminal.localQFTStressPaid Terminal.canonicalTerminalBoundary ≡ true
localStressPaidRegression = refl

pointwiseEnergyConditionsPaidRegression :
  Terminal.pointwiseEnergyConditionFingerprintPaid Terminal.canonicalTerminalBoundary ≡ true
pointwiseEnergyConditionsPaidRegression = refl

concreteScaleStillOpenRegression :
  Terminal.concreteCanonicalSetoidScaleWitnessPaid Terminal.canonicalTerminalBoundary ≡ false
concreteScaleStillOpenRegression = refl

qiStillOpenRegression :
  Terminal.sameObjectQuantumInequalityPaid Terminal.canonicalTerminalBoundary ≡ false
qiStillOpenRegression = refl

gravityStillOpenRegression :
  Terminal.semiclassicalGravityBackreactionPaid Terminal.canonicalTerminalBoundary ≡ false
gravityStillOpenRegression = refl

noMoreCardinalityPaymentRegression :
  Terminal.FurtherCardinalityFactorisationCountsAsPhysicalPayment → ⊥
noMoreCardinalityPaymentRegression = Terminal.furtherCardinalityIsNotPayment

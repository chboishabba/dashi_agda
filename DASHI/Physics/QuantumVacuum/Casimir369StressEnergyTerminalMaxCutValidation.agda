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

grqftRationalCrosswalkPaidRegression :
  Terminal.grqftRationalTensorCrosswalkPaid Terminal.canonicalTerminalBoundary ≡ true
grqftRationalCrosswalkPaidRegression = refl

activeProjectionCrossPollinationPaidRegression :
  Terminal.activeStressProjectionCrossPollinationPaid Terminal.canonicalTerminalBoundary ≡ true
activeProjectionCrossPollinationPaidRegression = refl

conditionalGRCompilerReusePaidRegression :
  Terminal.conditionalGRDiagnosticCompilerReusePaid Terminal.canonicalTerminalBoundary ≡ true
conditionalGRCompilerReusePaidRegression = refl

vacuumLambdaDiscriminatorPaidRegression :
  Terminal.vacuumLambdaDiscriminatorPaid Terminal.canonicalTerminalBoundary ≡ true
vacuumLambdaDiscriminatorPaidRegression = refl

sameCandidateHandoffInterfacePaidRegression :
  Terminal.sameCandidateUnificationHandoffInterfacePaid Terminal.canonicalTerminalBoundary ≡ true
sameCandidateHandoffInterfacePaidRegression = refl

concreteScaleStillOpenRegression :
  Terminal.concreteCanonicalSetoidScaleWitnessPaid Terminal.canonicalTerminalBoundary ≡ false
concreteScaleStillOpenRegression = refl

sameCandidateStressIdentificationStillOpenRegression :
  Terminal.casimirSharedStressIdentificationPaid Terminal.canonicalTerminalBoundary ≡ false
sameCandidateStressIdentificationStillOpenRegression = refl

commonActionIdentificationStillOpenRegression :
  Terminal.casimirCommonActionIdentificationPaid Terminal.canonicalTerminalBoundary ≡ false
commonActionIdentificationStillOpenRegression = refl

qiStillOpenRegression :
  Terminal.sameObjectQuantumInequalityPaid Terminal.canonicalTerminalBoundary ≡ false
qiStillOpenRegression = refl

gravityStillOpenRegression :
  Terminal.semiclassicalGravityBackreactionPaid Terminal.canonicalTerminalBoundary ≡ false
gravityStillOpenRegression = refl

unifiedQGStillClosedRegression :
  Terminal.unifiedQuantumGravityPromoted Terminal.canonicalTerminalBoundary ≡ false
unifiedQGStillClosedRegression = refl

firstUnificationBlockerRegression :
  Terminal.firstUnificationBlocker
  ≡ Terminal.missingCasimirSharedStressIdentificationInUnifiedCandidate
firstUnificationBlockerRegression = refl

noMoreCardinalityPaymentRegression :
  Terminal.FurtherCardinalityFactorisationCountsAsPhysicalPayment → ⊥
noMoreCardinalityPaymentRegression = Terminal.furtherCardinalityIsNotPayment

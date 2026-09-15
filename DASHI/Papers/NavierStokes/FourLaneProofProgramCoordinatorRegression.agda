module DASHI.Papers.NavierStokes.FourLaneProofProgramCoordinatorRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Papers.NavierStokes.FourLaneProofProgramExact as Program

-- RED-first coordinator contract. These are routing/status coordinates only;
-- they do not promote branch-local source receipts into Agda kernel receipts.

periodicBCommRecoveryModeIsActive :
  Program.periodicBCommutatorSpineRecoveryAssumptionActive
    Program.canonicalNSFourLaneProofProgram ≡ true
periodicBCommRecoveryModeIsActive =
  Program.periodicBCommutatorSpineRecoveryAssumptionActiveIsTrue

periodicBCommKernelReceiptStillAbsent :
  Program.periodicBCommutatorSpineCertificationObserved
    Program.canonicalNSFourLaneProofProgram ≡ false
periodicBCommKernelReceiptStillAbsent =
  Program.periodicBCommutatorSpineCertificationObservedIsFalse

-- R104's algebraic family/compiler is already recovered in-repo (R104/R372/R414).
periodicBPhaseR104CompilerRecovered :
  Program.periodicBPhaseR104CompilerRecovered
    Program.canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseR104CompilerRecovered =
  Program.periodicBPhaseR104CompilerRecoveredIsTrue

-- A concrete physical slice is still not recovered: the phase-sensitive
-- signed-production inequality remains an input field of R414.
periodicBPhasePhysicalR104StillOpen :
  Program.periodicBPhasePhysicalR104Recovered
    Program.canonicalNSFourLaneProofProgram ≡ false
periodicBPhasePhysicalR104StillOpen =
  Program.periodicBPhasePhysicalR104RecoveredIsFalse

-- R414 definitionally sets the Round104 integrable remainder to the literal
-- R406 remainder integral and reuses the R410 cutoff-uniform remainder bound.
periodicBPhaseR406WeldRecovered :
  Program.periodicBPhaseLiteralR406RemainderWeldRecovered
    Program.canonicalNSFourLaneProofProgram ≡ true
periodicBPhaseR406WeldRecovered =
  Program.periodicBPhaseLiteralR406RemainderWeldRecoveredIsTrue

periodicBPhaseSignedProductionEstimateStillOpen :
  Program.periodicBPhaseSignedProductionEstimateRecovered
    Program.canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseSignedProductionEstimateStillOpen =
  Program.periodicBPhaseSignedProductionEstimateRecoveredIsFalse

periodicBDiscoveryFrontierIsPhaseUnderRecoveryAssumption :
  Program.periodicBOnlyPhaseDiscoveryRemainsUnderCommRecoveryAssumption
    Program.canonicalNSFourLaneProofProgram ≡ true
periodicBDiscoveryFrontierIsPhaseUnderRecoveryAssumption =
  Program.periodicBOnlyPhaseDiscoveryRemainsUnderCommRecoveryAssumptionIsTrue

wholeSpaceAWaitsForPortabilityAudit :
  Program.wholeSpaceADeferredUntilPeriodicPortabilityAudit
    Program.canonicalNSFourLaneProofProgram ≡ true
wholeSpaceAWaitsForPortabilityAudit =
  Program.wholeSpaceADeferredUntilPeriodicPortabilityAuditIsTrue

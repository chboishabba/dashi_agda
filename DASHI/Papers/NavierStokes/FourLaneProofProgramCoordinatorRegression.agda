module DASHI.Papers.NavierStokes.FourLaneProofProgramCoordinatorRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Papers.NavierStokes.FourLaneProofProgramExact as Program

-- RED-first coordinator contract.  These are routing/status coordinates only;
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

periodicBPhaseR104StillOpen :
  Program.periodicBPhasePhysicalR104Recovered
    Program.canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseR104StillOpen =
  Program.periodicBPhasePhysicalR104RecoveredIsFalse

periodicBPhaseR406WeldStillOpen :
  Program.periodicBPhaseLiteralR406RemainderWeldRecovered
    Program.canonicalNSFourLaneProofProgram ≡ false
periodicBPhaseR406WeldStillOpen =
  Program.periodicBPhaseLiteralR406RemainderWeldRecoveredIsFalse

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

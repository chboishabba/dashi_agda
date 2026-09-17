module DASHI.Physics.YangMills.YMClayCanonicalContinuumOSWeldValidation where

-- Validation for replacing the generic parity continuation with existing
-- theorem-bearing Yang--Mills continuum and OS owners.  This root deliberately
-- does not claim `--safe`: the canonical recovery/terminal dependency spine on
-- current master is not uniformly safe-annotated.

import DASHI.Physics.YangMills.YMClayCanonicalContinuumOSWeldExact as Canonical

open Canonical

recoveryContinuumCompilerAvailable : Set
recoveryContinuumCompilerAvailable = RecoveryContinuumCompilerPresent

physicalMassGapEndgameAvailable : Set
physicalMassGapEndgameAvailable = PhysicalMassGapEndgamePresent

canonicalRecoveryWitness : RecoveryContinuumCompilerPresent
canonicalRecoveryWitness = recoveryContinuumCompilerPresent

canonicalEndgameWitness : PhysicalMassGapEndgamePresent
canonicalEndgameWitness = physicalMassGapEndgamePresent

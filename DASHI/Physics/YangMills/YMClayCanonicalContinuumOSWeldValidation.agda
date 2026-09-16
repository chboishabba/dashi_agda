{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCanonicalContinuumOSWeldValidation where

-- RED validation for replacing the generic parity continuation with existing
-- theorem-bearing Yang--Mills continuum and OS owners.

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

module DASHI.Physics.YangMills.BalabanPath4CoercivityCICanary where

import DASHI.Physics.YangMills.BalabanPath4AxisAverageNormContractionExact
import DASHI.Physics.YangMills.BalabanPath4DirectionalEnergyContractionExact
import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact

open import DASHI.Physics.YangMills.CompactLieProofLevel

-- This aggregate is intentionally tiny: the default-branch CI typechecks it
-- directly, so a success comment certifies the four new coercivity modules.
path4CoercivityCICanaryLevel : ProofLevel
path4CoercivityCICanaryLevel = machineChecked

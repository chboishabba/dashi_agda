{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMPaper3VacuumRecoveryGapProofAdapterExact where

------------------------------------------------------------------------
-- PAPER 3 / SHORTER VACUUM-RECOVERY GAP ROUTE
--
-- This is a sufficient lower-gap-survival route already proved generically in
-- the repository.  It is NOT identified with the manuscript's stronger H3a
-- trace-norm theorem.  Instead it records an alternative proof producer:
--
--   physical VacuumOrthogonalRecoverySystem
--     -> PhysicalVacuumGapAfterRecovery
--     -> downstream reconstruction / mass-gap extraction.
--
-- The physical Yang-Mills recovery-system producer remains open.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery

record Paper3RecoveryGapDownstream
    (system : Recovery.VacuumOrthogonalRecoverySystem) : Set₁ where
  field
    OSWightmanReconstruction : Set
    osWightmanReconstruction : OSWightmanReconstruction

    PositiveContinuumMassGap : Set

    positiveMassGapFromRecoveredGapAndReconstruction :
      Recovery.PhysicalVacuumGapAfterRecovery system →
      OSWightmanReconstruction →
      PositiveContinuumMassGap

open Paper3RecoveryGapDownstream public

paper3RecoveredVacuumGap :
  (system : Recovery.VacuumOrthogonalRecoverySystem) →
  Recovery.PhysicalVacuumGapAfterRecovery system
paper3RecoveredVacuumGap = Recovery.physicalVacuumGapAfterRecovery

paper3PositiveMassGapFromRecoveryRoute :
  ∀ {system} →
  (downstream : Paper3RecoveryGapDownstream system) →
  PositiveContinuumMassGap downstream
paper3PositiveMassGapFromRecoveryRoute {system} downstream =
  positiveMassGapFromRecoveredGapAndReconstruction downstream
    (paper3RecoveredVacuumGap system)
    (osWightmanReconstruction downstream)

paper3RecoveryGapCompilerLevel : ProofLevel
paper3RecoveryGapCompilerLevel = machineChecked

-- Generic recovery algebra is explicit; the actual physical YM recovery
-- system remains the first producer on this route.
paper3PhysicalVacuumRecoverySystemLevel : ProofLevel
paper3PhysicalVacuumRecoverySystemLevel = conditional

paper3RecoveryRouteOSWightmanLevel : ProofLevel
paper3RecoveryRouteOSWightmanLevel = conditional

paper3RecoveryRoutePositiveMassGapLevel : ProofLevel
paper3RecoveryRoutePositiveMassGapLevel = conditional

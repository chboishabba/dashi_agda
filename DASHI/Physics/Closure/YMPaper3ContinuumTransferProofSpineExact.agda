{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMPaper3ContinuumTransferProofSpineExact where

------------------------------------------------------------------------
-- PAPER 3 / TYPED CONTINUUM-TRANSFER PROOF SPINE
--
-- Paper 3 identifies the continuum Yang-Mills mass-gap route as
--
--   H3a trace/norm-resolvent transfer
--     -> RP.4 limiting-vacuum target
--     -> H3b vacuum-projection continuity
--     -> no spectral pollution
--     -> OS/Wightman reconstruction
--     -> positive continuum mass gap.
--
-- Earlier closure owners record this mainly as status / authority metadata.
-- This module exposes the same route as theorem-bearing dependent inputs.
-- It does not manufacture any analytic premise and does not promote Clay YM.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record Paper3ContinuumTransferSpine : Set₁ where
  field
    -- H3a: the manuscript's load-bearing continuum-transfer input.
    TraceNormTransferConvergence : Set
    NormResolventConvergence : Set

    h3aTraceNormTransfer :
      TraceNormTransferConvergence

    traceNormImpliesNormResolvent :
      TraceNormTransferConvergence → NormResolventConvergence

    -- RP.4 supplies the limiting vacuum target needed to state H3b honestly.
    LimitingVacuumTarget : Set
    limitingVacuumTarget : LimitingVacuumTarget

    -- H3b: finite vacuum projectors converge to that exact limiting vacuum.
    VacuumProjectionContinuity : LimitingVacuumTarget → Set
    h3bVacuumProjectionContinuity :
      VacuumProjectionContinuity limitingVacuumTarget

    -- No-spectral-pollution is a downstream theorem of H3a + H3b.
    NoSpectralPollution :
      NormResolventConvergence →
      VacuumProjectionContinuity limitingVacuumTarget →
      Set

    noSpectralPollutionFromH3aAndH3b :
      (normResolvent : NormResolventConvergence) →
      (vacuumContinuity :
        VacuumProjectionContinuity limitingVacuumTarget) →
      NoSpectralPollution normResolvent vacuumContinuity

    -- Reconstruction remains a distinct theorem-bearing intake.
    OSWightmanReconstruction : Set
    osWightmanReconstruction : OSWightmanReconstruction

    -- Terminal Paper-3 conclusion, still parameterized by actual analytic
    -- witnesses rather than Boolean authority flags.
    PositiveContinuumMassGap : Set

    positiveMassGapFromNoPollutionAndReconstruction :
      (normResolvent : NormResolventConvergence) →
      (vacuumContinuity :
        VacuumProjectionContinuity limitingVacuumTarget) →
      NoSpectralPollution normResolvent vacuumContinuity →
      OSWightmanReconstruction →
      PositiveContinuumMassGap

open Paper3ContinuumTransferSpine public

h3aNormResolvent :
  (spine : Paper3ContinuumTransferSpine) →
  NormResolventConvergence spine
h3aNormResolvent spine =
  traceNormImpliesNormResolvent spine (h3aTraceNormTransfer spine)

paper3NoSpectralPollution :
  (spine : Paper3ContinuumTransferSpine) →
  NoSpectralPollution spine
    (h3aNormResolvent spine)
    (h3bVacuumProjectionContinuity spine)
paper3NoSpectralPollution spine =
  noSpectralPollutionFromH3aAndH3b spine
    (h3aNormResolvent spine)
    (h3bVacuumProjectionContinuity spine)

paper3PositiveContinuumMassGap :
  (spine : Paper3ContinuumTransferSpine) →
  PositiveContinuumMassGap spine
paper3PositiveContinuumMassGap spine =
  positiveMassGapFromNoPollutionAndReconstruction spine
    (h3aNormResolvent spine)
    (h3bVacuumProjectionContinuity spine)
    (paper3NoSpectralPollution spine)
    (osWightmanReconstruction spine)

paper3ContinuumTransferCompilerLevel : ProofLevel
paper3ContinuumTransferCompilerLevel = machineChecked

-- The compiler above is closed, but the manuscript's actual analytic inputs
-- remain open until theorem-bearing inhabitants are supplied on the physical
-- Yang-Mills carrier.
paper3H3aPhysicalInputLevel : ProofLevel
paper3H3aPhysicalInputLevel = conditional

paper3H3bPhysicalInputLevel : ProofLevel
paper3H3bPhysicalInputLevel = conditional

paper3NoSpectralPollutionPhysicalInputLevel : ProofLevel
paper3NoSpectralPollutionPhysicalInputLevel = conditional

paper3OSWightmanPhysicalInputLevel : ProofLevel
paper3OSWightmanPhysicalInputLevel = conditional

paper3PositiveContinuumMassGapPhysicalLevel : ProofLevel
paper3PositiveContinuumMassGapPhysicalLevel = conditional

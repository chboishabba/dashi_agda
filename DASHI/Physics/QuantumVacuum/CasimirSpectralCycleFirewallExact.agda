module DASHI.Physics.QuantumVacuum.CasimirSpectralCycleFirewallExact where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Spectrum
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Kernel
import DASHI.Physics.QuantumVacuum.CasimirCycleAccounting as Cycle
import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- SPECTRAL CLOSURE != ENGINEERING CYCLE CLOSURE
--
-- Even a fully proved physical mode-spectrum / renormalised Casimir evaluation
-- establishes an equilibrium boundary-energy/stress law.  It does not by
-- itself construct switching, reset, dissipation accounting, or replication.
------------------------------------------------------------------------

record SpectralCasimirEstablished : Set₁ where
  field
    kernel : Kernel.CasimirScalarModel
    evaluation : Spectrum.ParallelPlateRenormalisedEvaluation kernel

open SpectralCasimirEstablished public

spectralCasimirClaim : SpectralCasimirEstablished → Surface.ExtractionClaim
spectralCasimirClaim established =
  Surface.mkExtractionClaim
    Surface.casimirRelaxation
    Surface.transient
    Surface.theoreticalProposal
    true true false false false

spectralCasimirStillNotCyclePromotable :
  (established : SpectralCasimirEstablished) →
  Surface.promotable? (spectralCasimirClaim established) ≡ false
spectralCasimirStillNotCyclePromotable established = refl

------------------------------------------------------------------------
-- A continuous cycle has an independent carrier and independent receipts.
------------------------------------------------------------------------

record SpectralAndCycleClosure : Set₁ where
  field
    spectral : SpectralCasimirEstablished
    cycle : Cycle.CasimirCycle
    continuousClosure : Cycle.ContinuousCasimirClosure cycle

open SpectralAndCycleClosure public

spectralAndCycleClosurePromotes :
  (closure : SpectralAndCycleClosure) →
  Surface.promotable?
    (Cycle.continuousClosureToExtractionClaim
      (cycle closure)
      (continuousClosure closure)) ≡ true
spectralAndCycleClosurePromotes closure =
  Cycle.continuousClosurePromotes
    (cycle closure)
    (continuousClosure closure)

------------------------------------------------------------------------
-- Explicit no-auto-promotion boundary.
------------------------------------------------------------------------

data SpectralEvaluationAutomaticallySuppliesCycleClosure : Set where

spectralEvaluationCannotAutoSupplyCycleClosure :
  SpectralEvaluationAutomaticallySuppliesCycleClosure → ⊥
spectralEvaluationCannotAutoSupplyCycleClosure ()

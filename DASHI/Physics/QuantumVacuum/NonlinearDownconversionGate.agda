module DASHI.Physics.QuantumVacuum.NonlinearDownconversionGate where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- Two detuned linear resonators do not by themselves establish collectible
-- low-frequency power.  The physically relevant bridge requires sideband
-- generation, coupling to a load, and detailed-balance discrimination.
------------------------------------------------------------------------

record DownconversionExperiment : Set where
  constructor mkDownconversionExperiment
  field
    twoResonancesObserved : Bool
    nonlinearMixingObserved : Bool
    sidebandObserved        : Bool
    loadCouplingObserved    : Bool
    detailedBalanceExcluded : Bool
    replicated              : Bool

record DownconversionWitness (e : DownconversionExperiment) : Set where
  constructor mkDownconversionWitness
  field
    resonancesClosed : DownconversionExperiment.twoResonancesObserved e ≡ true
    nonlinearClosed  : DownconversionExperiment.nonlinearMixingObserved e ≡ true
    sidebandClosed   : DownconversionExperiment.sidebandObserved e ≡ true
    loadClosed       : DownconversionExperiment.loadCouplingObserved e ≡ true
    balanceClosed    : DownconversionExperiment.detailedBalanceExcluded e ≡ true
    replicationClosed : DownconversionExperiment.replicated e ≡ true

downconversionClaim :
  (e : DownconversionExperiment) → DownconversionWitness e →
  Surface.ExtractionClaim
downconversionClaim e witness =
  Surface.mkExtractionClaim
    Surface.nonlinearVacuumDownconversion
    Surface.continuous
    Surface.replicatedExperiment
    true true true true true

downconversionWitnessPromotes :
  (e : DownconversionExperiment) → (witness : DownconversionWitness e) →
  Surface.promotable? (downconversionClaim e witness) ≡ true
downconversionWitnessPromotes e witness = refl

linearDetuningOnlyClaim : Surface.ExtractionClaim
linearDetuningOnlyClaim =
  Surface.mkExtractionClaim
    Surface.nonlinearVacuumDownconversion
    Surface.continuous
    Surface.numericalModel
    true false false false false

linearDetuningAloneBlocked :
  Surface.promotable? linearDetuningOnlyClaim ≡ false
linearDetuningAloneBlocked = refl

module DASHI.Physics.Chemistry.AtomicPeriodicTable369LiBeMinimalBasisHFExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- First simultaneous 1s/2s many-electron execution surface.
--
-- Basis data are externally sourced; the SCF implementation is repository
-- owned.  The result pays state tracking in a minimal basis, not complete-basis
-- convergence, correlation, relativity, spectroscopy, or a ternary identity.
------------------------------------------------------------------------

record MinimalBasisSourceReceipt : Set where
  constructor minimalBasisSourceReceipt
  field
    authority : String
    basisName : String
    referenceRole : String
    relationship : String

open MinimalBasisSourceReceipt public

sto3gBasisReceipt : MinimalBasisSourceReceipt
sto3gBasisReceipt =
  minimalBasisSourceReceipt
    "Basis Set Exchange; STO-3G reference lineage includes Hehre, Stewart and Pople (1969)"
    "STO-3G"
    "external orbital-basis parameter source"
    "supplies Gaussian exponents/contraction coefficients only; does not validate DASHI mechanism, SCF implementation, or basis convergence"

producerPath : String
producerPath = "scripts/atomic_li_be_sto3g_scf.py"

liExecutionEnergyHartree : String
liExecutionEnergyHartree = "-7.31552598128109"

beExecutionEnergyHartree : String
beExecutionEnergyHartree = "-14.35188047620202"

record LiBeMinimalBasisExecutionBoundary : Set where
  constructor liBeMinimalBasisExecutionBoundary
  field
    lithiumOneSAndTwoSTrackedSimultaneously : Bool
    berylliumOneSAndTwoSTrackedSimultaneously : Bool
    selfConsistentElectronInteractionIncluded : Bool
    explicitGaussianIntegralsOwnedByProducer : Bool
    externalBasisParametersAttributed : Bool
    completeBasisLimitPaid : Bool
    electronCorrelationPaid : Bool
    relativisticCorrectionsPaid : Bool
    experimentalIonizationCalibrationPaid : Bool
    ternaryToFullAtomIdentityPaid : Bool

open LiBeMinimalBasisExecutionBoundary public

canonicalLiBeMinimalBasisExecutionBoundary : LiBeMinimalBasisExecutionBoundary
canonicalLiBeMinimalBasisExecutionBoundary =
  liBeMinimalBasisExecutionBoundary
    true true true true true
    false false false false false

completeBasisLimitPaidIsFalse :
  completeBasisLimitPaid canonicalLiBeMinimalBasisExecutionBoundary ≡ false
completeBasisLimitPaidIsFalse = refl

ternaryToFullAtomIdentityPaidIsFalse :
  ternaryToFullAtomIdentityPaid canonicalLiBeMinimalBasisExecutionBoundary ≡ false
ternaryToFullAtomIdentityPaidIsFalse = refl

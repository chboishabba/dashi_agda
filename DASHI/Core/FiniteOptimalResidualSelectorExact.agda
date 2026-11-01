module DASHI.Core.FiniteOptimalResidualSelectorExact where

------------------------------------------------------------------------
-- FINITE OPTIMAL SAFE RESIDUAL SELECTOR
--
-- A concrete MDL-like optimization over certified-safe residual schemes for
-- the hidden-phase counterexample.  The zero-cost scheme is not certifiably
-- safe; retaining the C3 phase costs one and reopens exactly; redundant schemes
-- cost more.  Hence phase-only is the minimum-cost certified-safe residual in
-- this explicit finite family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Core.MinimalDynamicResidualExact as Minimal

------------------------------------------------------------------------
-- Candidate family.
------------------------------------------------------------------------

data ResidualScheme : Set where
  visibleOnly : ResidualScheme
  phaseOnly : ResidualScheme
  phasePlusVisibleCopy : ResidualScheme
  fullFineStateReceipt : ResidualScheme

schemeCost : ResidualScheme → Nat
schemeCost visibleOnly = zero
schemeCost phaseOnly = suc zero
schemeCost phasePlusVisibleCopy = suc (suc zero)
schemeCost fullFineStateReceipt = suc (suc (suc zero))

------------------------------------------------------------------------
-- Only schemes carrying at least the hidden phase receive a safety
-- certificate in this family.  The phase-only certificate is backed by the
-- exact reopening theorem already proved in MinimalDynamicResidualExact.
------------------------------------------------------------------------

data CertifiedSafe : ResidualScheme → Set where
  phaseOnlySafe : CertifiedSafe phaseOnly
  phasePlusVisibleSafe : CertifiedSafe phasePlusVisibleCopy
  fullFineStateSafe : CertifiedSafe fullFineStateReceipt

selectedScheme : ResidualScheme
selectedScheme = phaseOnly

selectedSchemeCostIsOne : schemeCost selectedScheme ≡ 1
selectedSchemeCostIsOne = refl

selectedReopensEveryHiddenPhaseState : Minimal.MinimalResidualCertificate
selectedReopensEveryHiddenPhaseState = Minimal.hiddenPhaseMinimalResidual

selectedCostNoGreaterThanAnyCertifiedSafe :
  (candidate : ResidualScheme) →
  CertifiedSafe candidate →
  schemeCost selectedScheme ≤ schemeCost candidate
selectedCostNoGreaterThanAnyCertifiedSafe phaseOnly phaseOnlySafe = s≤s z≤n
selectedCostNoGreaterThanAnyCertifiedSafe phasePlusVisibleCopy phasePlusVisibleSafe = s≤s z≤n
selectedCostNoGreaterThanAnyCertifiedSafe fullFineStateReceipt fullFineStateSafe = s≤s z≤n

record FiniteOptimalResidual : Set where
  constructor finiteOptimalResidual
  field
    selected : ResidualScheme
    selectedSafe : CertifiedSafe selected
    selectedMinimal :
      (candidate : ResidualScheme) →
      CertifiedSafe candidate →
      schemeCost selected ≤ schemeCost candidate

open FiniteOptimalResidual public

hiddenPhaseFiniteOptimalResidual : FiniteOptimalResidual
hiddenPhaseFiniteOptimalResidual =
  finiteOptimalResidual
    phaseOnly
    phaseOnlySafe
    selectedCostNoGreaterThanAnyCertifiedSafe

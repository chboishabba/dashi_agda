module DASHI.Analysis.CollatzSyracuseAffineTransferBarrierExact where

------------------------------------------------------------------------
-- FIRST EXACT AFFINE-TRANSFER CUTOFF BARRIER
--
-- EXTERNAL CROSS-POLLINATION SOURCE
-- Michael Sharpe, `msharpe248/collatz`, commit
--   ec8174b567d5cab4960024782210b5f5db02bd3a
-- files
--   lean/Collatz/AffinePairReturn.lean
--   lean/Collatz/RequestCutoff.lean
-- defines the transfer
--
--   A(u) : ReachesOne (3*u+2) -> ReachesOne (27*u+20)
--
-- and identifies u=546 as the first request beyond the certified U=511
-- cutoff route (equivalently 3^9 = 36*546+27).
--
-- ATTRIBUTION FIREWALL
-- The interface and barrier identification are externally sourced.  The
-- literal shortcut-Syracuse certificates below are independently evaluated on
-- DASHI's existing `SyracuseExact` carrier.  No Lean proof object is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Stop

------------------------------------------------------------------------
-- Same affine-transfer coordinate used by the external source.
------------------------------------------------------------------------

affineSource : Nat → Syracuse.PositiveNat
affineSource u = Syracuse.positiveNat (3 * u + 1)

affineTarget : Nat → Syracuse.PositiveNat
affineTarget u = Syracuse.positiveNat (27 * u + 19)

AffineTransfer : Nat → Set
AffineTransfer u = Stop.ReachesOne (affineSource u) → Stop.ReachesOne (affineTarget u)

affineSourceToNat :
  (u : Nat) →
  Syracuse.toNat (affineSource u) ≡ 3 * u + 2
affineSourceToNat u = refl

affineTargetToNat :
  (u : Nat) →
  Syracuse.toNat (affineTarget u) ≡ 27 * u + 20
affineTargetToNat u = refl

------------------------------------------------------------------------
-- First cutoff barrier u=546.
--
-- 27*546+20 = 14762.  Seven literal shortcut steps give 346, already below
-- the stalled cutoff 511.  More strongly, the target itself reaches 1 in 30
-- shortcut steps, so this transfer instance is unconditional.
------------------------------------------------------------------------

barrier546Target : affineTarget 546 ≡ Syracuse.positiveNat 14761
barrier546Target = refl

barrier546DropsBelow511 :
  Syracuse.syracuseIterate 7 (affineTarget 546)
  ≡ Syracuse.positiveNat 345
barrier546DropsBelow511 = refl

barrier546TargetReachesOne :
  Stop.ReachesOne (affineTarget 546)
barrier546TargetReachesOne = 30 , refl

affineTransfer546 : AffineTransfer 546
affineTransfer546 sourceStops = barrier546TargetReachesOne

-- Exact request arithmetic reported by the external cutoff analysis.
barrier546RequestIdentity : 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 ≡ 36 * 546 + 27
barrier546RequestIdentity = refl

record AffineTransferBarrierBoundary : Set where
  constructor affineTransferBarrierBoundary
  field
    affineTransferCarrierOwned : Nat
    externalBarrierPinned : Nat
    literalSevenStepDropOwned : Nat
    literalTargetStoppingOwned : Nat
    firstBarrierTransferOwned : Nat
    allTransferInstancesOwned : Nat

canonicalAffineTransferBarrierBoundary : AffineTransferBarrierBoundary
canonicalAffineTransferBarrierBoundary =
  affineTransferBarrierBoundary 1 1 1 1 1 0

module DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59 where

------------------------------------------------------------------------
-- ROUND 59 — physical source anchor for the HH-bad Duhamel lane.
--
-- This package binds the shellwise terms to one time-dependent physical
-- shell balance.  It is intentionally not an analytic witness: the literal
-- trajectory authority remains an explicit field, so this module cannot
-- manufacture a transfer from arbitrary rational functions or toy data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact as Time
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalTransferSurfaceRound58 as Transfer
import DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 as Threshold

record PhysicalLocalizedDuhamelSource : Set₁ where
  field
    physicalShellData : Time.PhysicalTimeDependentShellBalance Nat
    shellAt : Nat → Nat

    -- These are selectors on the sampled physical balance, not free shell
    -- sequences.  Their literal PDE meanings are supplied by the authority
    -- field below.
    defectSelector inheritedSelector generatedSelector leakageSelector :
      Shell.DynamicPhysicalShellBalance → ℚ

    parameter : Threshold.PositiveThreshold
    ceiling alpha beta : ℚ
    literalTrajectoryAuthority :
      Time.LiteralTrajectoryShellAuthority physicalShellData

open PhysicalLocalizedDuhamelSource public

defectAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
defectAt source q =
  defectSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

inheritedAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
inheritedAt source q =
  inheritedSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

generatedAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
generatedAt source q =
  generatedSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

leakageAt : PhysicalLocalizedDuhamelSource → Nat → ℚ
leakageAt source q =
  leakageSelector source
    (Time.balanceAt (physicalShellData source) (shellAt source q))

asLocalizedSource :
  PhysicalLocalizedDuhamelSource → Transfer.LocalizedDuhamelSource
asLocalizedSource source = record
  { parameter = parameter source
  ; defectRate = defectAt source
  ; inheritedCoefficient = inheritedAt source
  ; generated = generatedAt source
  ; leakage = leakageAt source
  ; ceiling = ceiling source
  ; alpha = alpha source
  ; beta = beta source
  }

physicalSourceUsesOneShellTrajectory : Bool
physicalSourceUsesOneShellTrajectory = true

physicalSourceUsesOneShellTrajectoryIsTrue :
  physicalSourceUsesOneShellTrajectory ≡ true
physicalSourceUsesOneShellTrajectoryIsTrue = refl

-- The authority is still open; no A transfer is promoted by this source
-- package alone.
physicalLocalizedDuhamelSourceConstructed : Bool
physicalLocalizedDuhamelSourceConstructed = false

physicalLocalizedDuhamelSourceConstructedIsFalse :
  physicalLocalizedDuhamelSourceConstructed ≡ false
physicalLocalizedDuhamelSourceConstructedIsFalse = refl

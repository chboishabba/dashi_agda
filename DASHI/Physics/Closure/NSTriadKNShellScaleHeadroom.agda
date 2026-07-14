module DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom where

open import Agda.Builtin.Nat using (Nat; _*_; suc)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (*-mono-≤; ≤-refl)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Shell-scale headroom: a reusable condition that the scale squared
-- beats the Stage-3 error constant.
--
-- Two canonical constructors:
--   headroomFromRawN  — the scale is N² (raw shell index)
--   headroomFromSucN  — the scale is (suc N)² (successor/dyadic scaling)
--
-- The only property needed downstream:
--   scaleSq ≥ 2   (since stage3ErrorConstant = 1, margin needs A > 1)

record ShellScaleHeadroom (N : Nat) : Set where
  constructor mkShellScaleHeadroom
  field
    scaleSq : Nat
    scaleSqBeatsStage3 : 2 ≤ scaleSq

open ShellScaleHeadroom public

record CompatibilityScale (N : Nat) : Set where
  constructor mkCompatibilityScale
  field
    scaleSq : Nat
    scaleHeadroom : 2 ≤ scaleSq

open CompatibilityScale public

compatibilityScaleFromHeadroom :
  {N : Nat} → ShellScaleHeadroom N → CompatibilityScale N
compatibilityScaleFromHeadroom hr =
  mkCompatibilityScale (ShellScaleHeadroom.scaleSq hr)
    (ShellScaleHeadroom.scaleSqBeatsStage3 hr)

headroomFromRawN :
  (N : Nat) → 2 ≤ N * N → ShellScaleHeadroom N
headroomFromRawN N h =
  mkShellScaleHeadroom (N * N) h

headroomFromSucN :
  (N : Nat) → 2 ≤ (suc N * suc N) → ShellScaleHeadroom N
headroomFromSucN N h =
  mkShellScaleHeadroom (suc N * suc N) h

------------------------------------------------------------------------
-- Reusable Rayleigh margin from scale headroom.
--
-- If scaleSq ≥ 2, then for all carriers:
--
--   2 * residueEnergy x ≤ scaleSq * residueEnergy x
--
-- This is the core inequality that the NegativeFrameRayleighMarginCore
-- needs (with baseGapConstant = 2), independent of whether the scale
-- comes from raw N² or (suc N)².

rayleighMarginFromScaleHeadroom :
  {N : Nat} →
  (hr : ShellScaleHeadroom N) →
  (x : ResidueNorm.ResidueEnergyCarrier N) →
  2 * ResidueNorm.residueEnergy x
    ≤ scaleSq hr * ResidueNorm.residueEnergy x
rayleighMarginFromScaleHeadroom hr x =
  *-mono-≤ (scaleSqBeatsStage3 hr) (≤-refl {ResidueNorm.residueEnergy x})

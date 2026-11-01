module DASHI.Algebra.MoonshinePlusOneAnalogue where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import CRTPeriod as CRT
import JFixedPoint as J
import DASHI.Algebra.MoonshineBridge as MB

------------------------------------------------------------------------
-- Moonshine +1 analogue row.
--
-- This module only indexes the existing 196883 -> 196884 witnesses from
-- CRTPeriod, JFixedPoint, and MoonshineBridge.

record MoonshinePlusOneAnalogueRow : Set₁ where
  constructor mkMoonshinePlusOneAnalogueRow
  field
    analogueLabel :
      String

    periodReference :
      Nat

    moonshineCoefficientReference :
      Nat

    existingBridgeReference :
      CRT.period + 1 ≡ J.contract J.unit-obs

    scalarBridgeSurface :
      MB.MoonshineScalarBridge

    analogueCandidateOnly :
      Bool

    analogueCandidateOnlyIsTrue :
      analogueCandidateOnly ≡ true

open MoonshinePlusOneAnalogueRow public

canonicalMoonshinePlusOneAnalogueRow :
  MoonshinePlusOneAnalogueRow
canonicalMoonshinePlusOneAnalogueRow =
  mkMoonshinePlusOneAnalogueRow
    "196883 + 1 identity-section analogy"
    CRT.period
    MB.moonshineCoefficient
    MB.MoonshineBridge
    MB.moonshineScalarBridgeSurface
    true
    refl


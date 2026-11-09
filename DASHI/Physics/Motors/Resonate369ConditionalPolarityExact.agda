module DASHI.Physics.Motors.Resonate369ConditionalPolarityExact where

------------------------------------------------------------------------
-- CONDITIONAL symbolic winding/pole signs; no CAD measurements.
-- Source contexts: Holmstrom/Resonate369 Dodecatron and C07 winding
-- descriptions. Neither clockwise winding labels nor magnet polarity
-- are independently measured in this module.
--
-- Two complementary reversals compensate at a selected terminal.
-- This is an elementary Boolean sign law, NOT measured generator
-- output, an AC waveform theorem, or a claimed power result.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

flip : Bool → Bool
flip true = false
flip false = true

flipInvolution : (b : Bool) → flip (flip b) ≡ b
flipInvolution true = refl
flipInvolution false = refl

-- true denotes negative parity; false denotes positive parity.
-- Polarity conventions must eventually be calibrated to selected
-- magnet and coil terminal orientation measurements.
xor : Bool → Bool → Bool
xor false b = b
xor true b = flip b

-- Sign of a chosen winding-terminal flux contribution. A terminal
-- convention can reverse the observable voltage sign.
effectiveSign : Bool → Bool → Bool → Bool
effectiveSign pole winding terminal =
  xor (xor pole winding) terminal

pairedReversalPreservesSign :
  (pole winding terminal : Bool) →
  effectiveSign (flip pole) (flip winding) terminal
  ≡ effectiveSign pole winding terminal
pairedReversalPreservesSign true true true = refl
pairedReversalPreservesSign true true false = refl
pairedReversalPreservesSign true false true = refl
pairedReversalPreservesSign true false false = refl
pairedReversalPreservesSign false true true = refl
pairedReversalPreservesSign false true false = refl
pairedReversalPreservesSign false false true = refl
pairedReversalPreservesSign false false false = refl

reversingTerminalFlipsSign :
  (pole winding terminal : Bool) →
  effectiveSign pole winding (flip terminal)
  ≡ flip (effectiveSign pole winding terminal)
reversingTerminalFlipsSign true true true = refl
reversingTerminalFlipsSign true true false = refl
reversingTerminalFlipsSign true false true = refl
reversingTerminalFlipsSign true false false = refl
reversingTerminalFlipsSign false true true = refl
reversingTerminalFlipsSign false true false = refl
reversingTerminalFlipsSign false false true = refl
reversingTerminalFlipsSign false false false = refl

-- A single magnet reversal without changing winding or terminals
-- reverses the predicted sign. This is a useful negative control.
reversingOnlyPoleFlipsSign :
  (pole winding terminal : Bool) →
  effectiveSign (flip pole) winding terminal
  ≡ flip (effectiveSign pole winding terminal)
reversingOnlyPoleFlipsSign true true true = refl
reversingOnlyPoleFlipsSign true true false = refl
reversingOnlyPoleFlipsSign true false true = refl
reversingOnlyPoleFlipsSign true false false = refl
reversingOnlyPoleFlipsSign false true true = refl
reversingOnlyPoleFlipsSign false true false = refl
reversingOnlyPoleFlipsSign false false true = refl
reversingOnlyPoleFlipsSign false false false = refl

-- Therefore paired alternation *can* align series voltages under a
-- common terminal convention. Whether actual coils do so stays open.

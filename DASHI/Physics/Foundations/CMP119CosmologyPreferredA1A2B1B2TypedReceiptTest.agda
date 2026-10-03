{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredA1A2B1B2TypedReceiptTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsTypedReceiptsExact as Typed
import DASHI.Physics.Foundations.CMP119CosmologyPreferredA1A2B1B2RouteExact as Route
import DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailThresholdToExpansionExact as Terminal

-- A2 must be the actual Wilson/OS-admissible selected R109 cylinder surface,
-- not merely an arbitrary pair-to-observable meaning socket.
a2PinsPublishedWilsonOSAdmissibility :
  Typed.a2ExactReceiptPinsPublishedWilsonOSAdmissibility ≡ true
a2PinsPublishedWilsonOSAdmissibility = refl

-- B2 must store the literal preferred threshold
--   c_V < -(M_ERB + Tail_109(k))
-- rather than only its downstream strict-envelope consequence.
b2StoresLiteralPreferredThreshold :
  Typed.b2ExactReceiptStoresLiteralVacuumThreshold ≡ true
b2StoresLiteralPreferredThreshold = refl

b2ThresholdStillDerivesStrictEnvelope :
  Typed.b2LiteralThresholdCompilesToStrictEnvelope ≡ true
b2ThresholdStillDerivesStrictEnvelope = refl

-- The route below B1+B2 remains the already-owned compiler chain.
negativeR136CompilerAlreadyPresent :
  Route.b1b2CompileToNegativeRationalR136 ≡ true
negativeR136CompilerAlreadyPresent = refl

terminalAccelerationCompilerAlreadyPresent :
  Route.terminalConsumerAlreadyCompilesNegativeR136ToMatterAcceleration ≡ true
terminalAccelerationCompilerAlreadyPresent = refl

exactTypedB2ReceiptFeedsTerminalAcceleration :
  Terminal.typedPreferredB2ReceiptCompilesToMatterAcceleration ≡ true
exactTypedB2ReceiptFeedsTerminalAcceleration = refl

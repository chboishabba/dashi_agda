{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyParetoMaxCut20261003DExact where

------------------------------------------------------------------------
-- TERMINAL PARETO OVERLAY D / SOURCE-ENVELOPE CUT.
--
-- Overlay C correctly counted five physical leaves.  The newest compiler does
-- NOT reduce that count.  It only shrinks the preferred sign consumer state:
--
--   B1 direct completion tail
--   + finite Eq.(2.23) upper compiler
--      => embed Q_R136 <= embed ((M_ERB + c_V) + Tail_R109(k)).
--
-- Hence finite D_Gamma is no longer a terminal sign coordinate.  B1 and B2 are
-- nevertheless still two independent physical source payments:
--
--   B1  source/completion comparison,
--   B2  source-native strict negativity of the Eq.(2.23) envelope.
--
-- Reconstruction remains the same two leaves and the anomaly fallback remains
-- the one-sided R136 <= selected-anomaly comparison from overlay C.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

data ReconstructionResidual : Set where
  e1-r144-canonical-b4-signed-readout-covariance : ReconstructionResidual
  e2e4-r109-pair-source-semantics-evaluator : ReconstructionResidual

data PreferredSignPhysicalResidual : Set where
  b1-r136-direct-source-completion-tail : PreferredSignPhysicalResidual
  b2-eq223-source-envelope-strict-negativity : PreferredSignPhysicalResidual

data AlternateSignPhysicalResidual : Set where
  c-r136-embedded-response-below-selected-anomaly-trace :
    AlternateSignPhysicalResidual

reconstructionResidualCount : Nat
reconstructionResidualCount = 2

preferredSignPhysicalResidualCount : Nat
preferredSignPhysicalResidualCount = 2

alternateSignPhysicalResidualCount : Nat
alternateSignPhysicalResidualCount = 1

totalTerminalPhysicalResidualCount : Nat
totalTerminalPhysicalResidualCount = 5

finiteDGammaStillTerminalSignCoordinate : Bool
finiteDGammaStillTerminalSignCoordinate = false

finiteEq223UpperIsCompilerInputToSourceEnvelope : Bool
finiteEq223UpperIsCompilerInputToSourceEnvelope = true

sourceEnvelopeCompressionMergesB1AndB2PhysicalPayments : Bool
sourceEnvelopeCompressionMergesB1AndB2PhysicalPayments = false

preferredTerminalResponseCoordinateIsR136BelowSourceEnvelope : Bool
preferredTerminalResponseCoordinateIsR136BelowSourceEnvelope = true

preferredStrictSignStillNeedsSourceNativeEnvelopeNegativity : Bool
preferredStrictSignStillNeedsSourceNativeEnvelopeNegativity = true

anomalyFallbackStillOneOneSidedPhysicalComparison : Bool
anomalyFallbackStillOneOneSidedPhysicalComparison = true

remainingSignWorkIsSourcePhysicsNotRepresentation : Bool
remainingSignWorkIsSourcePhysicsNotRepresentation = true

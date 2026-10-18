module DASHI.Analysis.RiemannG2AdaptiveCutoffCrossingCompatibilityLeanDonorExact where

------------------------------------------------------------------------
-- NATURAL ADAPTIVE CUTOFF: CROSSING + ARBITRARY FAR ACCURACY
--
-- Companion Lean source now proves the domain-neutral theorem:
--
--   Lambda > 0
--   epsilon > 0
--   far(J) -> 0
--   ---------------------------------------------
--   exists J : Nat,
--     1 <= J
--     and pi/2 < J*Lambda
--     and far(J) < epsilon.
--
-- Thus quarter-period crossing and arbitrarily sharp far-shell accuracy are not
-- competing asymptotic requirements.  The remaining RH payment is to instantiate
-- this theorem with the literal farShellBound / target taper and transport that
-- selected natural J into the exact final near/far carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record AdaptiveCutoffCrossingLeanReceipt : Set where
  constructor adaptive-cutoff-crossing-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    crossingTheorem : String
    jointExistenceTheorem : String
    sourceCommit : String
    regressionCommit : String

open AdaptiveCutoffCrossingLeanReceipt public

currentAdaptiveCutoffCrossingLeanReceipt : AdaptiveCutoffCrossingLeanReceipt
currentAdaptiveCutoffCrossingLeanReceipt =
  adaptive-cutoff-crossing-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannAdaptiveCutoffCrossingCompatibility.lean"
    "Synthesis/RiemannAdaptiveCutoffCrossingCompatibilityRegression.lean"
    "Synthesis.eventually_quarterPeriodCrossing"
    "Synthesis.exists_nat_cutoff_crossing_and_small"
    "49bbe08c68767007010a15da004f9eac486b7ade"
    "b291a8d58d0250f1528b8dca7f628eaadb1f83a7"

record AdaptiveCutoffCrossingBoundary : Set where
  constructor adaptive-cutoff-crossing-boundary
  field
    crossingAndFarAccuracyAsymptoticallyCompatible : Bool
    genericNaturalCutoffExistenceSourceWritten : Bool
    literalFarShellInstantiationPaid : Bool
    literalTaperCrossingInstantiationPaid : Bool
    exactFinalCarrierCutoffTransportPaid : Bool
    rhDerivedHere : Bool

open AdaptiveCutoffCrossingBoundary public

canonicalAdaptiveCutoffCrossingBoundary : AdaptiveCutoffCrossingBoundary
canonicalAdaptiveCutoffCrossingBoundary =
  adaptive-cutoff-crossing-boundary
    true
    true
    false
    false
    false
    false

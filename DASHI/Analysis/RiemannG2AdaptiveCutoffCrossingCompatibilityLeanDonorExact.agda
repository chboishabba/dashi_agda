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
    nearSignNoGoPath : String
    crossingExcludesSignWindowTheorem : String
    canonicalSignWindowCutoffTheorem : String
    selectedCrossingCannotPayNearSignTheorem : String
    sourceCommit : String
    regressionCommit : String
    nearSignNoGoCommit : String

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
    "Synthesis/RiemannAdaptiveCutoffNearSignNoGo.lean"
    "Synthesis.quarterPeriodCrossing_excludes_signWindow"
    "Synthesis.canonical_signWindow_implies_cutoff_le"
    "Synthesis.selected_crossing_cutoff_cannot_pay_centeredNearSign"
    "49bbe08c68767007010a15da004f9eac486b7ade"
    "b291a8d58d0250f1528b8dca7f628eaadb1f83a7"
    "a95e2a5c53e73dfe0c1d3579b6a576bf5f34d051"

record AdaptiveCutoffCrossingBoundary : Set where
  constructor adaptive-cutoff-crossing-boundary
  field
    crossingAndFarAccuracyAsymptoticallyCompatible : Bool
    genericNaturalCutoffExistenceSourceWritten : Bool
    literalFarShellInstantiationPaid : Bool
    literalTaperCrossingInstantiationPaid : Bool
    exactFinalCarrierCutoffTransportPaid : Bool
    crossingSelectorInsideCenteredNearSignWindow : Bool
    directAdaptiveCutoffNearSignWeldPaid : Bool
    canonicalFixedSupportSignWindowForcesLinearCutoff : Bool
    horizontalSquareFarRateAloneClosesR2 : Bool
    repairMustPreserveHorizontalSquareInsideSignWindowOrChangeSignArgument : Bool
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
    false
    false
    true
    false
    true
    false


------------------------------------------------------------------------
-- NORMALIZED CURRENT CUT
--
-- The generic adaptive selector and the centered near-sign theorem have
-- opposite cutoff requirements on one fixed support:
--
--   crossing selector:  pi/2 < J * Lambda
--   centered near sign: J * Lambda <= pi/2
--
-- Companion Lean proves this incompatibility directly.  For the canonical
-- support Lambda_t = 9*pi/(4*t), the near-sign premise also forces
-- J <= 2*t/9.  Therefore the displacement-adaptive far atom cannot be welded
-- directly to the existing centered-near sign proof on the fixed canonical
-- support.
--
-- This is a source/provenance boundary.  Lean proof terms are not Agda proofs.
------------------------------------------------------------------------

adaptiveCrossingSelectorLeavesNearSignWindow :
  AdaptiveCutoffCrossingBoundary.crossingSelectorInsideCenteredNearSignWindow
    canonicalAdaptiveCutoffCrossingBoundary ≡ false
adaptiveCrossingSelectorLeavesNearSignWindow = refl

directAdaptiveCutoffNearSignWeldStillOpen :
  AdaptiveCutoffCrossingBoundary.directAdaptiveCutoffNearSignWeldPaid
    canonicalAdaptiveCutoffCrossingBoundary ≡ false
directAdaptiveCutoffNearSignWeldStillOpen = refl

canonicalNearSignWindowForcesLinearCutoff :
  AdaptiveCutoffCrossingBoundary.canonicalFixedSupportSignWindowForcesLinearCutoff
    canonicalAdaptiveCutoffCrossingBoundary ≡ true
canonicalNearSignWindowForcesLinearCutoff = refl

horizontalSquareFarRateIsNotWholeR2Closure :
  AdaptiveCutoffCrossingBoundary.horizontalSquareFarRateAloneClosesR2
    canonicalAdaptiveCutoffCrossingBoundary ≡ false
horizontalSquareFarRateIsNotWholeR2Closure = refl

repairMustChangeScaleOrSignArgument :
  AdaptiveCutoffCrossingBoundary.repairMustPreserveHorizontalSquareInsideSignWindowOrChangeSignArgument
    canonicalAdaptiveCutoffCrossingBoundary ≡ true
repairMustChangeScaleOrSignArgument = refl

------------------------------------------------------------------------
-- O / R / C / S / L / P / G / F frame
------------------------------------------------------------------------

record AdaptiveCutoffNearSignZKPFrame : Set where
  constructor adaptive-cutoff-near-sign-zkp-frame
  field
    O : String
    R : String
    C : String
    S : String
    L : String
    P : String
    G : String
    F : String
    preconditionsExplicit : Bool
    invariantsExplicit : Bool
    postconditionsExplicit : Bool

open AdaptiveCutoffNearSignZKPFrame public

canonicalAdaptiveCutoffNearSignZKPFrame : AdaptiveCutoffNearSignZKPFrame
canonicalAdaptiveCutoffNearSignZKPFrame =
  adaptive-cutoff-near-sign-zkp-frame
    "O: preserve the literal final RH carrier and isolate the smallest unpaid high analytic cut"
    "R: reuse the adaptive far donor, centered near-sign donor, reflection-pair signal, and current R2 frontier before extension"
    "C: one fixed-support cutoff cannot satisfy both pi/2 < J*Lambda and J*Lambda <= pi/2"
    "S: keep the fixed canonical taper, final Off carrier, Gamma/pole semantics, and Lean-to-Agda proof boundary distinct"
    "L: prefer signed whole-response or horizontal-square-preserving estimates over absolute far-shell magnitude"
    "P: require Lambda>0, epsilon>0, far(J)->0, centered taper nonnegativity source, and exact same-carrier transport before promotion"
    "G: Pareto priority, snowball search, Ibrahim provenance, and max-cut scheduling do not create theorem authority"
    "F: close only by an a^2-preserving literal residual theorem inside the sign window, a displacement-dependent support, or signed cancellation beyond the quarter period"
    true
    true
    true

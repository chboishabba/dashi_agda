module DASHI.Analysis.RiemannG2NormalizedRvMSmoothMainDecompositionLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NORMALIZED SMOOTH RvM MAIN-TERM DECOMPOSITION
--
-- Companion Lean now isolates the dangerous q-independent logarithmic mode.
--
-- For t>0 and q>-1:
--
--   log ( t(1+q)/(2*pi) )
--     =
--   log ( t/(2*pi) ) + log(1+q).
--
-- Hence the smooth normalized RvM density is exactly
--
--   constantMode(t) + logShape(q).
--
-- On every finite normalized q-grid, the signed pairing therefore splits
-- exactly into
--
--   constantMode(t) * sum phi_i
--     + sum logShape(q_i) phi_i.
--
-- If the grid test has exact zero total mass, the apparent log(t) term is
-- annihilated exactly.
--
-- A pre-existing companion Lean owner also proves whole-line Fourier
-- annihilation from the literal physical zero-mode gap, conditional on L1
-- integrability of the Fourier transform.  The remaining same-object theorem
-- is the transport from that whole-line Fourier statement to the actual
-- finite/truncated normalized q-grid used by the RvM consumer.  No such
-- transport is silently asserted here.
------------------------------------------------------------------------

record NormalizedRvMSmoothMainReceipt : Set where
  constructor normalized-rvm-smooth-main-receipt
  field
    repository : String
    branch : String
    zeroModeFourierPath : String
    smoothMainDecompositionPath : String
    smoothMainDecompositionCommit : String
    rootWiringCommit : String

open NormalizedRvMSmoothMainReceipt public

currentNormalizedRvMSmoothMainReceipt :
  NormalizedRvMSmoothMainReceipt
currentNormalizedRvMSmoothMainReceipt =
  normalized-rvm-smooth-main-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedRvMZeroModeFourier.lean"
    "Synthesis/RiemannNormalizedRvMSmoothMainDecomposition.lean"
    "ece5cbdf27b12d8479822112ac30888188d9a761"
    "fb33671ee1763e10069ad7cd1a8873d546f77e19"

record NormalizedRvMSmoothMainBoundary : Set where
  constructor normalized-rvm-smooth-main-boundary
  field
    physicalZeroModeGapSourceWritten : Bool
    wholeLineFourierZeroModeCompilerSourceWritten : Bool
    smoothLogDensityConstantPlusShapeSourceWritten : Bool
    finiteSignedMainPairDecompositionSourceWritten : Bool
    exactFiniteZeroModeCancellationCompilerSourceWritten : Bool

    wholeLineFourierIntegrabilityPaid : Bool
    cosineTransformSameObjectBridgePaid : Bool
    wholeLineToActualQGridTransportPaid : Bool
    residualLogShapeMainBoundPaid : Bool
    smoothRvMMainProducerFullyPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    rhDerivedHere : Bool

open NormalizedRvMSmoothMainBoundary public

canonicalNormalizedRvMSmoothMainBoundary :
  NormalizedRvMSmoothMainBoundary
canonicalNormalizedRvMSmoothMainBoundary =
  normalized-rvm-smooth-main-boundary
    true
    true
    true
    true
    true

    false
    false
    false
    false
    false

    false
    false
    false
    false

smoothMainAlgebraNowPaidAtSource :
  NormalizedRvMSmoothMainBoundary.finiteSignedMainPairDecompositionSourceWritten
    canonicalNormalizedRvMSmoothMainBoundary ≡ true
smoothMainAlgebraNowPaidAtSource = refl

actualGridTransportStillOpen :
  NormalizedRvMSmoothMainBoundary.wholeLineToActualQGridTransportPaid
    canonicalNormalizedRvMSmoothMainBoundary ≡ false
actualGridTransportStillOpen = refl

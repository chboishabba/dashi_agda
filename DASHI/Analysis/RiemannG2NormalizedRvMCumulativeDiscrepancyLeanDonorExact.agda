module DASHI.Analysis.RiemannG2NormalizedRvMCumulativeDiscrepancyLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CUMULATIVE RvM DISCREPANCY -> ABEL PREFIX
--
-- Companion Lean now removes a theorem-shape mismatch from the high-side
-- remainder lane.
--
-- If cumulative counts N_k and M_k are converted to literal successive
-- increments Delta N_i and Delta M_i, then:
--
--   sum_{i<=k} (Delta N_i - Delta M_i)
--     = N_k - M_k.
--
-- Therefore a theorem-bearing pointwise cumulative RvM error
--
--   |N_k - M_k| <= B
--
-- directly inhabits the prefix hypothesis of the existing finite Abel
-- compiler.  We no longer need a bespoke external theorem already stated in
-- increment-prefix language.
--
-- This is finite algebra only.  The actual zeta RvM discrepancy theorem is
-- still a genuine external/analytic producer and remains fail-closed.
------------------------------------------------------------------------

record NormalizedRvMCumulativeDiscrepancyReceipt : Set where
  constructor normalized-rvm-cumulative-discrepancy-receipt
  field
    repository : String
    branch : String
    path : String
    compilerCommit : String
    rootWiringCommit : String

open NormalizedRvMCumulativeDiscrepancyReceipt public

currentNormalizedRvMCumulativeDiscrepancyReceipt :
  NormalizedRvMCumulativeDiscrepancyReceipt
currentNormalizedRvMCumulativeDiscrepancyReceipt =
  normalized-rvm-cumulative-discrepancy-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedRvMCumulativeDiscrepancyCompiler.lean"
    "0dcfa9f32ee945cc9da4e6c429017a4cf38a0c03"
    "0f6233d95c0653a88061df59ac3716a54088037c"

record NormalizedRvMCumulativeDiscrepancyBoundary : Set where
  constructor normalized-rvm-cumulative-discrepancy-boundary
  field
    cumulativeIncrementDefinitionSourceWritten : Bool
    prefixTelescopingIdentitySourceWritten : Bool
    cumulativeDiscrepancyToAbelCompilerSourceWritten : Bool
    oneSidedMainPlusRemainderConsumerSourceWritten : Bool

    theoremBearingZetaRvMMainCountPaid : Bool
    theoremBearingZetaCumulativeDiscrepancyPaid : Bool
    normalizedActualCountSameObjectAttachmentPaid : Bool
    remainderContributionQuantitativelyClosed : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    rhDerivedHere : Bool

open NormalizedRvMCumulativeDiscrepancyBoundary public

canonicalNormalizedRvMCumulativeDiscrepancyBoundary :
  NormalizedRvMCumulativeDiscrepancyBoundary
canonicalNormalizedRvMCumulativeDiscrepancyBoundary =
  normalized-rvm-cumulative-discrepancy-boundary
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

standardCumulativeErrorShapeNowAccepted :
  NormalizedRvMCumulativeDiscrepancyBoundary.cumulativeDiscrepancyToAbelCompilerSourceWritten
    canonicalNormalizedRvMCumulativeDiscrepancyBoundary ≡ true
standardCumulativeErrorShapeNowAccepted = refl

externalRvMDiscrepancyStillOpen :
  NormalizedRvMCumulativeDiscrepancyBoundary.theoremBearingZetaCumulativeDiscrepancyPaid
    canonicalNormalizedRvMCumulativeDiscrepancyBoundary ≡ false
externalRvMDiscrepancyStillOpen = refl

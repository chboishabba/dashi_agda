module DASHI.Analysis.RiemannG2NormalizedRvMAbelCompilerLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NORMALIZED RvM / ABEL COMPILER
--
-- Companion Lean now owns the exact finite summation-by-parts consumer for the
-- one-dimensional normalized q-counting measure.
--
-- For remainder increments w_i and test values phi_i, define
--
--   P_k = sum_{i<=k} w_i.
--
-- Lean proves exactly
--
--   sum_{i=0}^n w_i phi_i
--     =
--   P_n phi_n
--     + sum_{i=0}^{n-1} P_i (phi_i-phi_{i+1}),
--
-- and therefore, if |P_k| <= B for every prefix,
--
--   |sum w_i phi_i|
--     <= B * ( |phi_n| + sum |phi_i-phi_{i+1}| ).
--
-- It also source-writes the exact main/remainder split
--
--   actualIncrement = mainIncrement + remainderIncrement
--
-- at pairing level:
--
--   actualPair = mainPair + remainderPair,
--
-- preserving the smooth main pairing with its sign and taking absolute values
-- only on the genuine cumulative counting remainder.
--
-- IMPORTANT FIREWALL
--
-- The repo currently owns only the unconditional local upper count producer
--
--   Zeta23.RvM.zetaZeroConfig_local_count.
--
-- The older Agda RiemannZeroCounting fields named
-- riemannVonMangoldtMainTerm and explicitErrorBound are abstract Set-valued
-- obligations, not theorem-bearing RvM producers. They are not used here.
--
-- Thus the remaining collective H2 inputs are now sharply separated:
--
--   1. a theorem-bearing smooth RvM main-count realization on the SAME
--      normalized q carrier;
--   2. a cumulative remainder-prefix bound for actual-main counts;
--   3. signed Fourier evaluation/cancellation of the smooth main pairing;
--   4. final explicit comparison with the already-owned literal Gamma deficit.
------------------------------------------------------------------------

record NormalizedRvMAbelCompilerReceipt : Set where
  constructor normalized-rvm-abel-compiler-receipt
  field
    repository : String
    branch : String
    abelCompilerPath : String
    mainRemainderPath : String
    abelCommit : String
    mainRemainderCommit : String
    rootWiringCommit : String

open NormalizedRvMAbelCompilerReceipt public

currentNormalizedRvMAbelCompilerReceipt :
  NormalizedRvMAbelCompilerReceipt
currentNormalizedRvMAbelCompilerReceipt =
  normalized-rvm-abel-compiler-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedCountingAbelCompiler.lean"
    "Synthesis/RiemannNormalizedRvMMainRemainderCompiler.lean"
    "2396fe028b9d82a9df156c7b3fcb451f04a3b8fb"
    "ee3bdd45a5df90ca00039d0af8d508e57a3ce4e5"
    "5557b4c1f187709a7250064f59ffa24a9bb8c037"

record NormalizedRvMAbelCompilerBoundary : Set where
  constructor normalized-rvm-abel-compiler-boundary
  field
    finiteAbelIdentitySourceWritten : Bool
    cumulativeRemainderVariationBoundSourceWritten : Bool
    exactMainRemainderPairSplitSourceWritten : Bool
    signedMainPairPreservedBeforeMajorization : Bool

    theoremBearingRvMMainCountRealizationPaid : Bool
    cumulativeActualMinusMainRemainderBoundPaid : Bool
    smoothMainPairFourierCancellationPaid : Bool
    explicitUniformGammaMarginLowerBoundPaid : Bool
    aggregateOffBelowGammaDeficitPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open NormalizedRvMAbelCompilerBoundary public

canonicalNormalizedRvMAbelCompilerBoundary :
  NormalizedRvMAbelCompilerBoundary
canonicalNormalizedRvMAbelCompilerBoundary =
  normalized-rvm-abel-compiler-boundary
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
    false

abelConsumerNowSourceWritten :
  NormalizedRvMAbelCompilerBoundary.cumulativeRemainderVariationBoundSourceWritten
    canonicalNormalizedRvMAbelCompilerBoundary ≡ true
abelConsumerNowSourceWritten = refl

mainRemainderSplitPreservesSignedMain :
  NormalizedRvMAbelCompilerBoundary.signedMainPairPreservedBeforeMajorization
    canonicalNormalizedRvMAbelCompilerBoundary ≡ true
mainRemainderSplitPreservesSignedMain = refl

rvMActualMinusMainRemainderStillOpen :
  NormalizedRvMAbelCompilerBoundary.cumulativeActualMinusMainRemainderBoundPaid
    canonicalNormalizedRvMAbelCompilerBoundary ≡ false
rvMActualMinusMainRemainderStillOpen = refl

rhStillFailClosed :
  NormalizedRvMAbelCompilerBoundary.rhDerivedHere
    canonicalNormalizedRvMAbelCompilerBoundary ≡ false
rhStillFailClosed = refl

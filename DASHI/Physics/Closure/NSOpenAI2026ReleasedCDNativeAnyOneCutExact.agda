module DASHI.Physics.Closure.NSOpenAI2026ReleasedCDNativeAnyOneCutExact where

------------------------------------------------------------------------
-- RELEASED C/D / NATIVE ANY-ONE TERMINAL CUT
--
-- The canonical Fefferman semantics and the released-comparator -> literal
-- C/D adapters are already internal Agda theorems.  Therefore the remaining
-- released-proof boundary can be stated without hashes, provenance tokens, or
-- arbitrary semantic carriers: an actual native proof term of EITHER released
-- comparator theorem is sufficient for the concrete literal run target.
--
-- This owner makes the disjunction explicit so C and D do not accidentally
-- become a "prove both" programme.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSConcreteFeffermanSemanticsExact as Concrete
import DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact as Run
import DASHI.Physics.Closure.NSConcreteReleasedCDNativeReconstructionExact as Native

data ReleasedCDNativeAlternative
    (K : Concrete.FeffermanAnalyticKernel) : Set₂ where
  releasedC :
    Native.ConcreteReleasedComparatorCTheorem K →
    ReleasedCDNativeAlternative K

  releasedD :
    Native.ConcreteReleasedComparatorDTheorem K →
    ReleasedCDNativeAlternative K

releasedCDAnyOneToRunTarget :
  ∀ {K} →
  ReleasedCDNativeAlternative K →
  Run.ConcreteLiteralNSRunTarget K
releasedCDAnyOneToRunTarget (releasedC theorem) =
  Native.nativeReleasedComparatorCToRunTarget theorem
releasedCDAnyOneToRunTarget (releasedD theorem) =
  Native.nativeReleasedComparatorDToRunTarget theorem

releasedCAloneToRunTarget :
  ∀ {K} →
  Native.ConcreteReleasedComparatorCTheorem K →
  Run.ConcreteLiteralNSRunTarget K
releasedCAloneToRunTarget =
  Native.nativeReleasedComparatorCToRunTarget

releasedDAloneToRunTarget :
  ∀ {K} →
  Native.ConcreteReleasedComparatorDTheorem K →
  Run.ConcreteLiteralNSRunTarget K
releasedDAloneToRunTarget =
  Native.nativeReleasedComparatorDToRunTarget

------------------------------------------------------------------------
-- Machine-readable trust boundary.
------------------------------------------------------------------------

canonicalConcreteSemanticsAtReleasedBoundary : Bool
canonicalConcreteSemanticsAtReleasedBoundary = true

releasedComparatorAdapterToLiteralCClosed : Bool
releasedComparatorAdapterToLiteralCClosed = true

releasedComparatorAdapterToLiteralDClosed : Bool
releasedComparatorAdapterToLiteralDClosed = true

eitherReleasedAlternativeSuffices : Bool
eitherReleasedAlternativeSuffices = true

foreignReceiptCountsAsNativeProof : Bool
foreignReceiptCountsAsNativeProof = false

releasedAnalyticCandidateProofTermConstructedHere : Bool
releasedAnalyticCandidateProofTermConstructedHere = false

canonicalConcreteSemanticsAtReleasedBoundaryIsTrue :
  canonicalConcreteSemanticsAtReleasedBoundary ≡ true
canonicalConcreteSemanticsAtReleasedBoundaryIsTrue = refl

eitherReleasedAlternativeSufficesIsTrue :
  eitherReleasedAlternativeSuffices ≡ true
eitherReleasedAlternativeSufficesIsTrue = refl

foreignReceiptCountsAsNativeProofIsFalse :
  foreignReceiptCountsAsNativeProof ≡ false
foreignReceiptCountsAsNativeProofIsFalse = refl

releasedAnalyticCandidateProofTermConstructedHereIsFalse :
  releasedAnalyticCandidateProofTermConstructedHere ≡ false
releasedAnalyticCandidateProofTermConstructedHereIsFalse = refl

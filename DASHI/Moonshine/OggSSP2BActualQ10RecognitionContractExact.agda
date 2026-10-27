module DASHI.Moonshine.OggSSP2BActualQ10RecognitionContractExact where

------------------------------------------------------------------------
-- ACTUAL 2B TATE Q10 RECOGNITION CONTRACT
--
-- The Brauer screen and finite M22:2 ten-module computation are already paid.
-- What remains is not another character/count calculation: it is one literal
-- ten-dimensional quotient/subquotient on the actual 2B Tate head, with the
-- sourced outer involution descending to that SAME quotient.
--
-- This owner packages exactly that seam.  Every named obligation is paired
-- with an inhabitant, so constructing this record really pays the theorem
-- rather than merely naming a proposition type.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2BM22d2Completion10RuntimeReceiptExact as Finite

record ActualTateQ10Recognition : Set₁ where
  field
    Tate276 : Set
    Q10 : Set

    -- Concrete implementations may realize this through N <= S <= Tate276
    -- with S/N = Q10.  The proposition and its witness are both retained.
    ActualSubquotientReceipt : Set
    actualSubquotientReceipt : ActualSubquotientReceipt

    selectedFiniteKind : Finite.M22d2TenModuleKind
    FiniteKindIdentificationReceipt : Set
    finiteKindIdentificationReceipt : FiniteKindIdentificationReceipt

    outerAction : Q10 → Q10
    outerActionIsInvolution : (q : Q10) → outerAction (outerAction q) ≡ q

    -- Key C' obligation: the sourced M22:2 outer operator must induce this
    -- exact action on this exact quotient, not just an isomorphic J2^5 model.
    OuterActionDescentReceipt : Set
    sourcedOuterActionDescendsToSameQ : OuterActionDescentReceipt

open ActualTateQ10Recognition public

record ActualQ10AcquisitionBoundary : Set where
  constructor actual-q10-acquisition-boundary
  field
    brauerSemisimplifiedIngressPaid : Bool
    finiteTenCandidatesPaid : Bool
    finiteOuterJ2x5Paid : Bool
    actualQ10SameObjectPaid : Bool
    selectedTenKindPaid : Bool
    outerActionDescentPaid : Bool
    residualCount : Nat

open ActualQ10AcquisitionBoundary public

canonicalActualQ10AcquisitionBoundary : ActualQ10AcquisitionBoundary
canonicalActualQ10AcquisitionBoundary =
  actual-q10-acquisition-boundary
    true true true
    false false false
    3

-- The recognition record itself is now the single producer for all three
-- representation-side payments.  D's two sourced orientation decisions remain
-- independent by design.
record ActualQ10RecognitionClosure : Set₁ where
  field
    recognition : ActualTateQ10Recognition

open ActualQ10RecognitionClosure public

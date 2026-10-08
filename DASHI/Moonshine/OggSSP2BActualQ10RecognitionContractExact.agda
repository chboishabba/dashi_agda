module DASHI.Moonshine.OggSSP2BActualQ10RecognitionContractExact where

------------------------------------------------------------------------
-- ACTUAL 2B TATE Q10 RECOGNITION CONTRACT
--
-- The Brauer screen and finite M22:2 ten-module computation are already paid.
-- What remains is not another character/count calculation: it is one literal
-- ten-dimensional quotient/subquotient on the actual 2B Tate head, with the
-- sourced outer involution descending to that SAME quotient.
--
-- This owner packages exactly that seam.  It does not manufacture the missing
-- subquotient or identify tenA/tenB by numerical coincidence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2BM22d2Completion10RuntimeReceiptExact as Finite

record ActualTateQ10Recognition : Set₁ where
  field
    Tate276 : Set
    Q10 : Set

    -- Proof-relevant actual same-object/subquotient data.  The concrete module
    -- implementation may realize these via N <= S <= Tate276 with S/N = Q10.
    actualSubquotientReceipt : Set

    selectedFiniteKind : Finite.M22d2TenModuleKind
    finiteKindIdentificationReceipt : Set

    outerAction : Q10 → Q10
    outerActionIsInvolution : (q : Q10) → outerAction (outerAction q) ≡ q

    -- This is the key C' same-object obligation: the sourced M22:2 outer
    -- operator must be the action induced on this exact quotient, not merely
    -- an abstract J2^5 operator on an isomorphic ten-dimensional carrier.
    sourcedOuterActionDescendsToSameQ : Set

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

-- Once an ActualTateQ10Recognition exists, the old three representation-side
-- residuals collapse to compiler projections.  The two independent D-source
-- orientation decisions remain outside this record by design.
record ActualQ10RecognitionClosure : Set₁ where
  field
    recognition : ActualTateQ10Recognition
    actualQ10SameObjectPaid : Set
    selectedTenKindPaid : Set
    outerActionDescentPaid : Set

open ActualQ10RecognitionClosure public

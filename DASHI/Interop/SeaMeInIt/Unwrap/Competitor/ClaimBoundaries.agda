module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.ClaimBoundaries where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods

------------------------------------------------------------------------
-- Claim-boundary helpers
------------------------------------------------------------------------

boundaryForFamily : MethodFamily → ClaimBoundary
boundaryForFamily _ = standardBenchmarkBoundary

familyBoundaryForKind : MethodKind → ClaimBoundary
familyBoundaryForKind method =
  boundaryForFamily (methodFamily method)

record FamilyClaimBoundaryReceipt : Set where
  field
    methodKind : MethodKind
    family : MethodFamily
    familyMatches : family ≡ methodFamily methodKind
    allowed : FamilyAllowedClaims
    allowedMatches : allowed ≡ allowedClaims family
    boundary : ClaimBoundary
    noGlobalClaim :
      claimsGlobalOptimality boundary ≡ false
    noIsometryClaim :
      claimsIsometry boundary ≡ false
    noFakeInverseClaim :
      claimsTrueInverse boundary ≡ false
    plainReading : String

open FamilyClaimBoundaryReceipt public

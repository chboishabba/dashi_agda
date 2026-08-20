module DASHI.Algebra.SimpleRootLocalParameterExact where

------------------------------------------------------------------------
-- GENERIC SIMPLE-ROOT LOCAL PARAMETER THEOREM
--
-- If a branch function satisfies locally
--
--   branchValue = coordinateDifference * derivativeUnit,
--
-- with
--
--   v(coordinateDifference)=1,
--   v(derivativeUnit)=0,
--
-- then multiplicativity forces
--
--   v(branchValue)=1.
--
-- This is the reusable valuation step behind the exceptional Legendre j=0
-- identity
--
--   q(lambda)-q(lambda0)
--     = (lambda-lambda0)(lambda+lambda0-1),
--
-- and the j=1728 linear branches.  It is pure valuation algebra: it does not
-- construct a p-adic lift, prove a residue is nonzero, or choose a uniformizer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified

record SimpleRootLocalParameter
    {A : Set}
    (V : Ramified.MultiplicativeNatValuation A) : Set where
  field
    coordinateDifference : A
    derivativeUnit : A
    branchValue : A

    coordinateDifferenceDepthOne :
      Ramified.valuation V coordinateDifference ≡ 1

    derivativeUnitDepthZero :
      Ramified.valuation V derivativeUnit ≡ 0

    simpleRootFactorization :
      branchValue ≡ Ramified.mul V coordinateDifference derivativeUnit

open SimpleRootLocalParameter public

simpleRootBranchDepthOne :
  {A : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (S : SimpleRootLocalParameter V) →
  Ramified.valuation V (branchValue S) ≡ 1
simpleRootBranchDepthOne V S =
  trans
    (cong (Ramified.valuation V) (simpleRootFactorization S))
    (trans
      (Ramified.valuationMul V
        (coordinateDifference S) (derivativeUnit S))
      (trans
        (cong
          (λ d → d + Ramified.valuation V (derivativeUnit S))
          (coordinateDifferenceDepthOne S))
        (trans
          (cong (λ d → 1 + d) (derivativeUnitDepthZero S))
          refl)))

record SimpleRootLocalParameterBoundary : Set where
  field
    simpleRootFactorizationProofRelevant : Bool
    coordinateDepthOneRequired : Bool
    derivativeUnitDepthZeroRequired : Bool
    branchDepthOneDerived : Bool
    padicCoordinateLiftConstructedHere : Bool
    derivativeResidueNonzeroProvedHere : Bool

canonicalSimpleRootLocalParameterBoundary : SimpleRootLocalParameterBoundary
canonicalSimpleRootLocalParameterBoundary = record
  { simpleRootFactorizationProofRelevant = true
  ; coordinateDepthOneRequired = true
  ; derivativeUnitDepthZeroRequired = true
  ; branchDepthOneDerived = true
  ; padicCoordinateLiftConstructedHere = false
  ; derivativeResidueNonzeroProvedHere = false
  }

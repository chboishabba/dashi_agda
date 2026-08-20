module DASHI.Algebra.UniformizerCoordinateDifferenceExact where

------------------------------------------------------------------------
-- GENERIC UNIFORMIZER COORDINATE-DIFFERENCE THEOREM
--
-- In a discretely valued local field/ring, a coordinate difference is depth
-- one when it is one uniformizer times a unit:
--
--   delta = pi * epsilon,
--   v(pi)=1,
--   residue(epsilon) != 0.
--
-- `ResidueDetectedUnitValuationExact` turns the residue witness into
-- v(epsilon)=0; multiplicativity then derives v(delta)=1.
--
-- This is the correct generic target for an exceptional Legendre p-adic lift.
-- No Q_p, subtraction, Hensel lifting or Teichmuller theory is constructed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.ResidueDetectedUnitValuationExact as Residue

record UniformizerCoordinateDifference
    {A R : Set}
    (V : Ramified.MultiplicativeNatValuation A) : Set where
  field
    residueValuation : Residue.ResidueDetectedUnitValuation A R
    valuationCompatibility :
      (x : A) →
      Ramified.valuation V x ≡ Residue.valuation residueValuation x

    uniformizer : A
    unitFactor : A
    coordinateDifference : A

    uniformizerDepthOne : Ramified.valuation V uniformizer ≡ 1
    unitResidueNonzero : Residue.ResidueUnitWitness residueValuation unitFactor

    coordinateFactorization :
      coordinateDifference ≡ Ramified.mul V uniformizer unitFactor

open UniformizerCoordinateDifference public

unitFactorDepthZero :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (C : UniformizerCoordinateDifference V) →
  Ramified.valuation V (unitFactor C) ≡ 0
unitFactorDepthZero V C =
  trans
    (valuationCompatibility C (unitFactor C))
    (Residue.residueUnitHasDepthZero
      (residueValuation C)
      (unitFactor C)
      (unitResidueNonzero C))

coordinateDifferenceDepthOne :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (C : UniformizerCoordinateDifference V) →
  Ramified.valuation V (coordinateDifference C) ≡ 1
coordinateDifferenceDepthOne V C =
  trans
    (cong (Ramified.valuation V) (coordinateFactorization C))
    (trans
      (Ramified.valuationMul V (uniformizer C) (unitFactor C))
      (trans
        (cong
          (λ d → d + Ramified.valuation V (unitFactor C))
          (uniformizerDepthOne C))
        (trans
          (cong (λ d → 1 + d) (unitFactorDepthZero V C))
          refl)))

record UniformizerCoordinateDifferenceBoundary : Set where
  field
    uniformizerDepthOneSourceFacing : Bool
    unitResidueNonzeroSourceFacing : Bool
    coordinateFactorizationSourceFacing : Bool
    unitDepthZeroDerived : Bool
    coordinateDepthOneDerived : Bool
    QpConstructedHere : Bool
    HenselLiftConstructedHere : Bool

canonicalUniformizerCoordinateDifferenceBoundary :
  UniformizerCoordinateDifferenceBoundary
canonicalUniformizerCoordinateDifferenceBoundary = record
  { uniformizerDepthOneSourceFacing = true
  ; unitResidueNonzeroSourceFacing = true
  ; coordinateFactorizationSourceFacing = true
  ; unitDepthZeroDerived = true
  ; coordinateDepthOneDerived = true
  ; QpConstructedHere = false
  ; HenselLiftConstructedHere = false
  }

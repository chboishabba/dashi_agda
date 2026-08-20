module DASHI.Moonshine.LegendreJExceptionalLocalValuationCutsetExact where

------------------------------------------------------------------------
-- EXCEPTIONAL LEGENDRE LOCAL-VALUATION CUTSET
--
-- The exact polynomial identities are owned by
-- `LegendreJExceptionalPolynomialFactorizationExact`:
--
--   j numerator                    ~ q(lambda)^3,
--   j numerator - 1728 denominator ~
--       (lambda-2)^2 (lambda+1)^2 (2lambda-1)^2.
--
-- Therefore the ramification exponent is no longer a free analytic input.
-- A source-native local p-adic adapter chooses the actual exceptional branch
-- and supplies
--
--   localJDifference = localUnit * localParameter^branchExponent,
--   valuation(localParameter)=1.
--
-- Unit depth can be supplied directly, or more source-natively it can be
-- DERIVED from a nonzero residue witness through
-- `ResidueDetectedUnitValuationExact`.
--
-- The generic valuation algebra then derives the local J depth from the
-- ALGEBRAIC branch exponent.  This does not construct p-adic lifts, residue
-- fields, the depth-one parameter theorem, or Dwork's A1 transfer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.ResidueDetectedUnitValuationExact as Residue
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre

record ExceptionalLegendreLocalSharpness
    {A : Set}
    (V : Ramified.MultiplicativeNatValuation A)
    (branch : Legendre.ExceptionalLegendreBranch) : Set where
  field
    localUnit : A
    localParameter : A
    localJDifference : A

    localUnitDepthZero : Ramified.valuation V localUnit ≡ 0
    localParameterDepthOne : Ramified.valuation V localParameter ≡ 1

    localJFactorization :
      localJDifference
      ≡ Ramified.mul V localUnit
          (Ramified.pow V localParameter
            (Legendre.exceptionalRamificationExponent branch))

open ExceptionalLegendreLocalSharpness public

------------------------------------------------------------------------
-- Residue-facing producer: replace a bare v(unit)=0 assertion by the finite
-- local-ring statement residue(unit) != 0 whenever the domain has such a map.
-- Projections remain qualified to avoid shadowing the legacy local-sharpness
-- field names exported above.
------------------------------------------------------------------------

record ExceptionalLegendreLocalResidueSharpness
    {A R : Set}
    (V : Ramified.MultiplicativeNatValuation A)
    (branch : Legendre.ExceptionalLegendreBranch) : Set where
  field
    residueValuation : Residue.ResidueDetectedUnitValuation A R
    valuationCompatibility :
      (x : A) →
      Ramified.valuation V x
      ≡ Residue.valuation residueValuation x

    localUnit : A
    localParameter : A
    localJDifference : A

    localUnitResidueNonzero :
      Residue.ResidueUnitWitness residueValuation localUnit

    localParameterDepthOne : Ramified.valuation V localParameter ≡ 1

    localJFactorization :
      localJDifference
      ≡ Ramified.mul V localUnit
          (Ramified.pow V localParameter
            (Legendre.exceptionalRamificationExponent branch))

residueSharpnessToLocalSharpness :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  ExceptionalLegendreLocalResidueSharpness V branch →
  ExceptionalLegendreLocalSharpness V branch
residueSharpnessToLocalSharpness V branch S = record
  { ExceptionalLegendreLocalSharpness.localUnit =
      ExceptionalLegendreLocalResidueSharpness.localUnit S
  ; ExceptionalLegendreLocalSharpness.localParameter =
      ExceptionalLegendreLocalResidueSharpness.localParameter S
  ; ExceptionalLegendreLocalSharpness.localJDifference =
      ExceptionalLegendreLocalResidueSharpness.localJDifference S
  ; ExceptionalLegendreLocalSharpness.localUnitDepthZero =
      trans
        (ExceptionalLegendreLocalResidueSharpness.valuationCompatibility S
          (ExceptionalLegendreLocalResidueSharpness.localUnit S))
        (Residue.residueUnitHasDepthZero
          (ExceptionalLegendreLocalResidueSharpness.residueValuation S)
          (ExceptionalLegendreLocalResidueSharpness.localUnit S)
          (ExceptionalLegendreLocalResidueSharpness.localUnitResidueNonzero S))
  ; ExceptionalLegendreLocalSharpness.localParameterDepthOne =
      ExceptionalLegendreLocalResidueSharpness.localParameterDepthOne S
  ; ExceptionalLegendreLocalSharpness.localJFactorization =
      ExceptionalLegendreLocalResidueSharpness.localJFactorization S
  }

asRamifiedSharpCoefficient :
  {A : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  ExceptionalLegendreLocalSharpness V branch →
  Ramified.RamifiedSharpCoefficient
    V (Legendre.exceptionalRamificationExponent branch)
asRamifiedSharpCoefficient V branch S = record
  { Ramified.localUnit = localUnit S
  ; Ramified.localBranch = localParameter S
  ; Ramified.coefficient = localJDifference S
  ; Ramified.localUnitDepthZero = localUnitDepthZero S
  ; Ramified.localBranchDepthOne = localParameterDepthOne S
  ; Ramified.coefficientFactorization = localJFactorization S
  }

exceptionalLocalJDepthIsAlgebraicRamification :
  {A : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : ExceptionalLegendreLocalSharpness V branch) →
  Ramified.valuation V (localJDifference S)
  ≡ Legendre.exceptionalRamificationExponent branch
exceptionalLocalJDepthIsAlgebraicRamification V branch S =
  Ramified.ramifiedSharpCoefficientValuation
    V
    (Legendre.exceptionalRamificationExponent branch)
    (asRamifiedSharpCoefficient V branch S)

exceptionalResidueLocalJDepthIsAlgebraicRamification :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : ExceptionalLegendreLocalResidueSharpness V branch) →
  Ramified.valuation V
    (ExceptionalLegendreLocalResidueSharpness.localJDifference S)
  ≡ Legendre.exceptionalRamificationExponent branch
exceptionalResidueLocalJDepthIsAlgebraicRamification V branch S =
  exceptionalLocalJDepthIsAlgebraicRamification
    V branch (residueSharpnessToLocalSharpness V branch S)

jZeroLocalJDepthThree :
  {A : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (S : ExceptionalLegendreLocalSharpness V Legendre.jZeroQuadraticBranch) →
  Ramified.valuation V (localJDifference S) ≡ 3
jZeroLocalJDepthThree V S =
  exceptionalLocalJDepthIsAlgebraicRamification
    V Legendre.jZeroQuadraticBranch S

j1728MinusTwoLocalJDepthTwo :
  {A : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (S : ExceptionalLegendreLocalSharpness V Legendre.j1728LambdaMinusTwo) →
  Ramified.valuation V (localJDifference S) ≡ 2
j1728MinusTwoLocalJDepthTwo V S =
  exceptionalLocalJDepthIsAlgebraicRamification
    V Legendre.j1728LambdaMinusTwo S

j1728PlusOneLocalJDepthTwo :
  {A : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (S : ExceptionalLegendreLocalSharpness V Legendre.j1728LambdaPlusOne) →
  Ramified.valuation V (localJDifference S) ≡ 2
j1728PlusOneLocalJDepthTwo V S =
  exceptionalLocalJDepthIsAlgebraicRamification
    V Legendre.j1728LambdaPlusOne S

j1728TwoLambdaMinusOneLocalJDepthTwo :
  {A : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (S : ExceptionalLegendreLocalSharpness V Legendre.j1728TwoLambdaMinusOne) →
  Ramified.valuation V (localJDifference S) ≡ 2
j1728TwoLambdaMinusOneLocalJDepthTwo V S =
  exceptionalLocalJDepthIsAlgebraicRamification
    V Legendre.j1728TwoLambdaMinusOne S

record LegendreJExceptionalLocalValuationCutsetBoundary : Set where
  field
    exceptionalBranchRequired : Bool
    ramificationExponentReadFromAlgebraicFactorization : Bool
    freeNumericRamificationExponentAcceptedFromSource : Bool
    unitDepthCanBeDerivedFromResidueNonvanishing : Bool
    residueFieldConstructedHere : Bool
    localParameterDepthOneStillSourceFacing : Bool
    localPadicFactorizationStillSourceFacing : Bool
    DworkA1TransferConstructedHere : Bool

canonicalLegendreJExceptionalLocalValuationCutsetBoundary :
  LegendreJExceptionalLocalValuationCutsetBoundary
canonicalLegendreJExceptionalLocalValuationCutsetBoundary = record
  { exceptionalBranchRequired = true
  ; ramificationExponentReadFromAlgebraicFactorization = true
  ; freeNumericRamificationExponentAcceptedFromSource = false
  ; unitDepthCanBeDerivedFromResidueNonvanishing = true
  ; residueFieldConstructedHere = false
  ; localParameterDepthOneStillSourceFacing = true
  ; localPadicFactorizationStillSourceFacing = true
  ; DworkA1TransferConstructedHere = false
  }

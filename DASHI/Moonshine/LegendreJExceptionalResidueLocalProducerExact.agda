module DASHI.Moonshine.LegendreJExceptionalResidueLocalProducerExact where

------------------------------------------------------------------------
-- PREFERRED EXCEPTIONAL LEGENDRE LOCAL PRODUCER
--
-- This module composes four independent algebraic layers:
--
--   * exact Legendre exceptional exponent/factorization;
--   * residue-nonzero -> valuation-zero unit detection;
--   * uniformizer-times-unit -> depth-one coordinate difference;
--   * simple-root depth-one propagation.
--
-- A source-native p-adic adapter therefore no longer supplies ANY of
--
--   v(outerUnit)=0,
--   v(lambda-lambda0)=1,
--   v(branchValue)=1
--
-- as primitive numeric assertions.  It supplies the more geometric data
--
--   coordinateDifference = uniformizer * coordinateUnit,
--   v(uniformizer)=1,
--   residue(coordinateUnit) != 0,
--   residue(derivativeUnit) != 0,
--   residue(outerUnit) != 0,
--   branchValue=coordinateDifference*derivativeUnit,
--   J-alpha=outerUnit*branchValue^e.
--
-- All three valuation statements are then derived, followed by
-- v(J-alpha)=e with e fixed algebraically by the selected Legendre branch.
--
-- No Q_p, residue field, lift, or Dwork A1 coefficient is constructed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.ResidueDetectedUnitValuationExact as Residue
import DASHI.Algebra.SimpleRootLocalParameterExact as Simple
import DASHI.Algebra.UniformizerCoordinateDifferenceExact as Uniformizer
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreJExceptionalLocalValuationCutsetExact as Local

record ExceptionalResidueLocalProducer
    {A R : Set}
    (V : Ramified.MultiplicativeNatValuation A)
    (branch : Legendre.ExceptionalLegendreBranch) : Set where
  field
    residueValuation : Residue.ResidueDetectedUnitValuation A R
    valuationCompatibility :
      (x : A) →
      Ramified.valuation V x
      ≡ Residue.valuation residueValuation x

    uniformizer : A
    coordinateUnit : A
    coordinateDifference : A

    uniformizerDepthOne : Ramified.valuation V uniformizer ≡ 1
    coordinateUnitResidueNonzero :
      Residue.ResidueUnitWitness residueValuation coordinateUnit
    coordinateFactorization :
      coordinateDifference ≡ Ramified.mul V uniformizer coordinateUnit

    derivativeUnit : A
    branchValue : A

    derivativeUnitResidueNonzero :
      Residue.ResidueUnitWitness residueValuation derivativeUnit

    simpleRootFactorization :
      branchValue ≡ Ramified.mul V coordinateDifference derivativeUnit

    outerUnit : A
    localJDifference : A

    outerUnitResidueNonzero :
      Residue.ResidueUnitWitness residueValuation outerUnit

    localJFactorization :
      localJDifference
      ≡ Ramified.mul V outerUnit
          (Ramified.pow V branchValue
            (Legendre.exceptionalRamificationExponent branch))

open ExceptionalResidueLocalProducer public

------------------------------------------------------------------------
-- Derived coordinate depth through one uniformizer and a residue unit.
------------------------------------------------------------------------

asUniformizerCoordinate :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Uniformizer.UniformizerCoordinateDifference V
asUniformizerCoordinate V branch P = record
  { Uniformizer.residueValuation = residueValuation P
  ; Uniformizer.valuationCompatibility = valuationCompatibility P
  ; Uniformizer.uniformizer = uniformizer P
  ; Uniformizer.unitFactor = coordinateUnit P
  ; Uniformizer.coordinateDifference = coordinateDifference P
  ; Uniformizer.uniformizerDepthOne = uniformizerDepthOne P
  ; Uniformizer.unitResidueNonzero = coordinateUnitResidueNonzero P
  ; Uniformizer.coordinateFactorization = coordinateFactorization P
  }

coordinateDifferenceDepthOne :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Ramified.valuation V (coordinateDifference P) ≡ 1
coordinateDifferenceDepthOne V branch P =
  Uniformizer.coordinateDifferenceDepthOne V
    (asUniformizerCoordinate V branch P)

------------------------------------------------------------------------
-- Derived unit depths.
------------------------------------------------------------------------

derivativeUnitDepthZero :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Ramified.valuation V (derivativeUnit P) ≡ 0
derivativeUnitDepthZero V branch P =
  trans
    (valuationCompatibility P (derivativeUnit P))
    (Residue.residueUnitHasDepthZero
      (residueValuation P)
      (derivativeUnit P)
      (derivativeUnitResidueNonzero P))

outerUnitDepthZero :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Ramified.valuation V (outerUnit P) ≡ 0
outerUnitDepthZero V branch P =
  trans
    (valuationCompatibility P (outerUnit P))
    (Residue.residueUnitHasDepthZero
      (residueValuation P)
      (outerUnit P)
      (outerUnitResidueNonzero P))

------------------------------------------------------------------------
-- Derived depth-one branch via the generic simple-root theorem.
------------------------------------------------------------------------

asSimpleRootParameter :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Simple.SimpleRootLocalParameter V
asSimpleRootParameter V branch P = record
  { Simple.coordinateDifference = coordinateDifference P
  ; Simple.derivativeUnit = derivativeUnit P
  ; Simple.branchValue = branchValue P
  ; Simple.coordinateDifferenceDepthOne = coordinateDifferenceDepthOne V branch P
  ; Simple.derivativeUnitDepthZero = derivativeUnitDepthZero V branch P
  ; Simple.simpleRootFactorization = simpleRootFactorization P
  }

branchValueDepthOne :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Ramified.valuation V (branchValue P) ≡ 1
branchValueDepthOne V branch P =
  Simple.simpleRootBranchDepthOne V (asSimpleRootParameter V branch P)

------------------------------------------------------------------------
-- Adapter to the existing local sharpness theorem.
------------------------------------------------------------------------

asExceptionalLocalSharpness :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Local.ExceptionalLegendreLocalSharpness V branch
asExceptionalLocalSharpness V branch P = record
  { Local.localUnit = outerUnit P
  ; Local.localParameter = branchValue P
  ; Local.localJDifference = localJDifference P
  ; Local.localUnitDepthZero = outerUnitDepthZero V branch P
  ; Local.localParameterDepthOne = branchValueDepthOne V branch P
  ; Local.localJFactorization = localJFactorization P
  }

preferredLocalJDepthIsAlgebraicExponent :
  {A R : Set} →
  (V : Ramified.MultiplicativeNatValuation A) →
  (branch : Legendre.ExceptionalLegendreBranch) →
  (P : ExceptionalResidueLocalProducer V branch) →
  Ramified.valuation V (localJDifference P)
  ≡ Legendre.exceptionalRamificationExponent branch
preferredLocalJDepthIsAlgebraicExponent V branch P =
  Local.exceptionalLocalJDepthIsAlgebraicRamification
    V branch (asExceptionalLocalSharpness V branch P)

record LegendreJExceptionalResidueLocalProducerBoundary : Set where
  field
    outerUnitDepthPrimitive : Bool
    coordinateDifferenceDepthOnePrimitive : Bool
    branchDepthOnePrimitive : Bool
    uniformizerDepthOneRequired : Bool
    coordinateUnitResidueNonzeroRequired : Bool
    derivativeResidueNonzeroRequired : Bool
    outerUnitResidueNonzeroRequired : Bool
    exactLocalFactorizationsRequired : Bool
    algebraicExponentReused : Bool
    localJDepthDerived : Bool
    DworkA1TransferConstructedHere : Bool

canonicalLegendreJExceptionalResidueLocalProducerBoundary :
  LegendreJExceptionalResidueLocalProducerBoundary
canonicalLegendreJExceptionalResidueLocalProducerBoundary = record
  { outerUnitDepthPrimitive = false
  ; coordinateDifferenceDepthOnePrimitive = false
  ; branchDepthOnePrimitive = false
  ; uniformizerDepthOneRequired = true
  ; coordinateUnitResidueNonzeroRequired = true
  ; derivativeResidueNonzeroRequired = true
  ; outerUnitResidueNonzeroRequired = true
  ; exactLocalFactorizationsRequired = true
  ; algebraicExponentReused = true
  ; localJDepthDerived = true
  ; DworkA1TransferConstructedHere = false
  }

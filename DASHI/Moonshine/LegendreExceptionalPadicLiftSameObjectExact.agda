module DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact where

------------------------------------------------------------------------
-- SAME-OBJECT RESIDUE -> p-ADIC LIFT INTERFACE FOR EXCEPTIONAL LEGENDRE POINTS
--
-- PRIMARY CONTEXT
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- DASHI CONTRIBUTION
--
-- The finite exceptional residue geometry is now explicit at p=5,7,11, while
-- `LegendreJExceptionalResidueLocalProducerExact` gives the generic valuation
-- consequences once a genuine local lift exists.  This file types the missing
-- SAME-OBJECT bridge between those two levels.
--
-- A source adapter must identify:
--
--   finite exceptional residue centre lambda_bar,
--   actual lifted centre lambda0,
--   actual nearby lifted coordinate lambda,
--   actual coordinate difference delta=lambda-lambda0,
--
-- through one reduction map.  The depth-one statement is not supplied as a
-- number: delta must factor as one uniformizer times a residue unit.
--
-- Likewise the derivative/complement and outer J unit are actual local
-- elements whose reductions are the finite nonzero residues selected by the
-- residue geometry.
--
-- This module deliberately does NOT construct Q_p, Hensel/Teichmuller lifts,
-- subtraction laws, or Dwork's analytic coefficient family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.ResidueDetectedUnitValuationExact as Residue
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreJExceptionalResidueLocalProducerExact as Preferred

------------------------------------------------------------------------
-- Finite residue-side roles.  Concrete p=5 and p=7,11 modules can supply these
-- values without being identified with the p-adic carrier itself.
------------------------------------------------------------------------

record ExceptionalFiniteResiduePoint (R : Set) : Set where
  field
    zero : R
    centre : R
    derivativeResidue : R
    outerUnitResidue : R

    derivativeResidueNonzero : derivativeResidue ≡ zero → ⊥
    outerUnitResidueNonzero : outerUnitResidue ≡ zero → ⊥

open ExceptionalFiniteResiduePoint public

------------------------------------------------------------------------
-- Same-object local lift.
------------------------------------------------------------------------

record ExceptionalPadicLift
    (branch : Legendre.ExceptionalLegendreBranch) : Set₁ where
  field
    PadicLocal : Set
    Residue : Set

    valuation : Ramified.MultiplicativeNatValuation PadicLocal
    residueValuation : Residue.ResidueDetectedUnitValuation PadicLocal Residue
    valuationCompatibility :
      (x : PadicLocal) →
      Ramified.valuation valuation x
      ≡ Residue.valuation residueValuation x

    finitePoint : ExceptionalFiniteResiduePoint Residue
    residueZeroMatches :
      Residue.residueZero residueValuation ≡ zero finitePoint

    -- Local coordinate data.
    subtract : PadicLocal → PadicLocal → PadicLocal
    liftedCoordinate : PadicLocal
    liftedCentre : PadicLocal
    coordinateDifference : PadicLocal

    liftedCentreReducesToFiniteCentre :
      Residue.residue residueValuation liftedCentre ≡ centre finitePoint
    liftedCoordinateReducesToFiniteCentre :
      Residue.residue residueValuation liftedCoordinate ≡ centre finitePoint

    coordinateDifferenceIsActualDifference :
      coordinateDifference ≡ subtract liftedCoordinate liftedCentre

    -- One-uniformizer displacement, giving depth one constructively.
    uniformizer : PadicLocal
    coordinateUnit : PadicLocal
    uniformizerDepthOne : Ramified.valuation valuation uniformizer ≡ 1
    coordinateUnitResidueNonzero :
      Residue.ResidueUnitWitness residueValuation coordinateUnit
    coordinateFactorization :
      coordinateDifference
      ≡ Ramified.mul valuation uniformizer coordinateUnit

    -- Actual local simple-root factor and its finite residue identity.
    derivativeUnit : PadicLocal
    branchValue : PadicLocal
    derivativeReducesToFiniteDerivative :
      Residue.residue residueValuation derivativeUnit
      ≡ derivativeResidue finitePoint
    branchSimpleFactorization :
      branchValue
      ≡ Ramified.mul valuation coordinateDifference derivativeUnit

    -- Actual outer rational-function unit and its finite residue identity.
    outerUnit : PadicLocal
    localJDifference : PadicLocal
    outerUnitReducesToFiniteOuterUnit :
      Residue.residue residueValuation outerUnit
      ≡ outerUnitResidue finitePoint

    localJFactorization :
      localJDifference
      ≡ Ramified.mul valuation outerUnit
          (Ramified.pow valuation branchValue
            (Legendre.exceptionalRamificationExponent branch))

open ExceptionalPadicLift public

------------------------------------------------------------------------
-- Turn finite nonzero residue certificates into the proof-relevant witnesses
-- consumed by the preferred local producer.
------------------------------------------------------------------------

derivativeResidueWitness :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (L : ExceptionalPadicLift branch) →
  Residue.ResidueUnitWitness (residueValuation L) (derivativeUnit L)
derivativeResidueWitness branch L = record
  { Residue.residueNonzero = λ derivativeZero →
      derivativeResidueNonzero (finitePoint L)
        (trans
          (sym (derivativeReducesToFiniteDerivative L))
          (trans derivativeZero (residueZeroMatches L)))
  }

outerResidueWitness :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (L : ExceptionalPadicLift branch) →
  Residue.ResidueUnitWitness (residueValuation L) (outerUnit L)
outerResidueWitness branch L = record
  { Residue.residueNonzero = λ outerZero →
      outerUnitResidueNonzero (finitePoint L)
        (trans
          (sym (outerUnitReducesToFiniteOuterUnit L))
          (trans outerZero (residueZeroMatches L)))
  }

------------------------------------------------------------------------
-- Preferred producer is now derived from ONE same-object lift authority.
------------------------------------------------------------------------

asPreferredLocalProducer :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (L : ExceptionalPadicLift branch) →
  Preferred.ExceptionalResidueLocalProducer (valuation L) branch
asPreferredLocalProducer branch L = record
  { Preferred.residueValuation = residueValuation L
  ; Preferred.valuationCompatibility = valuationCompatibility L
  ; Preferred.uniformizer = uniformizer L
  ; Preferred.coordinateUnit = coordinateUnit L
  ; Preferred.coordinateDifference = coordinateDifference L
  ; Preferred.uniformizerDepthOne = uniformizerDepthOne L
  ; Preferred.coordinateUnitResidueNonzero = coordinateUnitResidueNonzero L
  ; Preferred.coordinateFactorization = coordinateFactorization L
  ; Preferred.derivativeUnit = derivativeUnit L
  ; Preferred.branchValue = branchValue L
  ; Preferred.derivativeUnitResidueNonzero = derivativeResidueWitness branch L
  ; Preferred.simpleRootFactorization = branchSimpleFactorization L
  ; Preferred.outerUnit = outerUnit L
  ; Preferred.localJDifference = localJDifference L
  ; Preferred.outerUnitResidueNonzero = outerResidueWitness branch L
  ; Preferred.localJFactorization = localJFactorization L
  }

liftedLocalJDepthIsAlgebraicExponent :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (L : ExceptionalPadicLift branch) →
  Ramified.valuation (valuation L) (localJDifference L)
  ≡ Legendre.exceptionalRamificationExponent branch
liftedLocalJDepthIsAlgebraicExponent branch L =
  Preferred.preferredLocalJDepthIsAlgebraicExponent
    (valuation L) branch (asPreferredLocalProducer branch L)

record LegendreExceptionalPadicLiftSameObjectBoundary : Set where
  field
    finiteResidueAndPadicCarriersSeparated : Bool
    liftedCentreReductionRequired : Bool
    nearbyCoordinateSameResidueRequired : Bool
    actualCoordinateDifferenceRequired : Bool
    oneUniformizerFactorizationRequired : Bool
    derivativeResidueIdentityRequired : Bool
    outerUnitResidueIdentityRequired : Bool
    localJDepthDerivedAfterLift : Bool
    QpConstructedHere : Bool
    HenselOrTeichmullerConstructionHere : Bool
    DworkA1TransferConstructedHere : Bool

canonicalLegendreExceptionalPadicLiftSameObjectBoundary :
  LegendreExceptionalPadicLiftSameObjectBoundary
canonicalLegendreExceptionalPadicLiftSameObjectBoundary = record
  { finiteResidueAndPadicCarriersSeparated = true
  ; liftedCentreReductionRequired = true
  ; nearbyCoordinateSameResidueRequired = true
  ; actualCoordinateDifferenceRequired = true
  ; oneUniformizerFactorizationRequired = true
  ; derivativeResidueIdentityRequired = true
  ; outerUnitResidueIdentityRequired = true
  ; localJDepthDerivedAfterLift = true
  ; QpConstructedHere = false
  ; HenselOrTeichmullerConstructionHere = false
  ; DworkA1TransferConstructedHere = false
  }

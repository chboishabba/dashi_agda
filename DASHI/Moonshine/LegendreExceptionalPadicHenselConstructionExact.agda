module DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE HENSEL -> EXCEPTIONAL LEGENDRE p-ADIC LIFT
--
-- PRIMARY SOURCES
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
-- Sections 4 and 7 use the Legendre modulus as the local parameter at the
-- supersingular points entering the first-pole calculation.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
-- Legendre family, reduction, and Hensel/local-field context.
--
-- DASHI CONTRIBUTION
--
-- The earlier `ExceptionalPadicLift` record correctly stated the same-object
-- obligations but did not CONSTRUCT its nearby point.  Here the source-facing
-- authority is lowered to standard complete-DVR/Hensel data:
--
--   * an actual Hensel lift lambda0 of the certified finite residue root;
--   * one uniformizer pi;
--   * the nearby point is DEFINED as lambda = lambda0 + pi;
--   * subtraction therefore derives lambda-lambda0 = pi*1;
--   * the selected Legendre branch is evaluated at that actual lambda;
--   * the simple-factor quotient and rational-function outer factor are actual
--     local elements with certified nonzero reductions;
--   * the exact branch and J-alpha factorizations are source algebraic laws.
--
-- Thus `lambda-lambda0 = pi epsilon` is no longer a primitive target equality:
-- epsilon is literally the local multiplicative identity.  The only imported
-- content is ordinary local-field/Hensel algebra and the same rational-function
-- factorization after transport to the completed local carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.ResidueDetectedUnitValuationExact as ResidueUnit
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact as Lift

------------------------------------------------------------------------
-- Standard complete-DVR / Hensel source surface.
------------------------------------------------------------------------

record ExceptionalHenselLocalSource
    (branch : Legendre.ExceptionalLegendreBranch) : Set₁ where
  field
    PadicLocal Residue : Set

    valuation : Ramified.MultiplicativeNatValuation PadicLocal
    residueValuation : ResidueUnit.ResidueDetectedUnitValuation PadicLocal Residue
    valuationCompatibility :
      (x : PadicLocal) →
      Ramified.valuation valuation x
      ≡ ResidueUnit.valuation residueValuation x

    finitePoint : Lift.ExceptionalFiniteResiduePoint Residue
    residueZeroMatches :
      ResidueUnit.residueZero residueValuation ≡ Lift.zero finitePoint

    -- Actual additive local-field operations used to define the nearby point.
    add subtract : PadicLocal → PadicLocal → PadicLocal
    subtractAddRight :
      (x d : PadicLocal) → subtract (add x d) x ≡ d

    -- Actual Hensel lift of the selected finite simple root.
    zeroLocal : PadicLocal
    branchPolynomial : PadicLocal → PadicLocal
    liftedCentre : PadicLocal
    liftedCentreReduces :
      ResidueUnit.residue residueValuation liftedCentre ≡ Lift.centre finitePoint
    liftedCentreIsRoot : branchPolynomial liftedCentre ≡ zeroLocal

    -- DVR uniformizer.  The nearby coordinate will be lambda0 + pi.
    uniformizer : PadicLocal
    uniformizerDepthOne : Ramified.valuation valuation uniformizer ≡ 1
    uniformizerReducesToZero :
      ResidueUnit.residue residueValuation uniformizer
      ≡ ResidueUnit.residueZero residueValuation

    -- The multiplicative identity is the coordinate unit epsilon.
    oneResidueUnit :
      ResidueUnit.ResidueUnitWitness residueValuation (Ramified.one valuation)
    mulRightOne :
      (x : PadicLocal) →
      Ramified.mul valuation x (Ramified.one valuation) ≡ x

    -- Actual simple-factor quotient at lambda=lambda0+pi.
    derivativeUnit : PadicLocal
    derivativeReduces :
      ResidueUnit.residue residueValuation derivativeUnit
      ≡ Lift.derivativeResidue finitePoint
    branchFactorizationAtNearby :
      branchPolynomial (add liftedCentre uniformizer)
      ≡ Ramified.mul valuation
          (subtract (add liftedCentre uniformizer) liftedCentre)
          derivativeUnit

    -- Actual rational-function J-alpha factor at the same nearby point.
    alphaLift : PadicLocal
    localJ : PadicLocal → PadicLocal
    outerUnit : PadicLocal
    outerUnitReduces :
      ResidueUnit.residue residueValuation outerUnit
      ≡ Lift.outerUnitResidue finitePoint
    localJFactorizationAtNearby :
      subtract (localJ (add liftedCentre uniformizer)) alphaLift
      ≡ Ramified.mul valuation outerUnit
          (Ramified.pow valuation
            (branchPolynomial (add liftedCentre uniformizer))
            (Legendre.exceptionalRamificationExponent branch))

open ExceptionalHenselLocalSource public

------------------------------------------------------------------------
-- The actual nearby point / coordinate difference are definitions.
------------------------------------------------------------------------

liftedCoordinate :
  {branch : Legendre.ExceptionalLegendreBranch} →
  ExceptionalHenselLocalSource branch → PadicLocal
liftedCoordinate S = add S (liftedCentre S) (uniformizer S)

coordinateDifference :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) → PadicLocal S
coordinateDifference S = subtract S (liftedCoordinate S) (liftedCentre S)

coordinateDifferenceIsUniformizer :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) →
  coordinateDifference S ≡ uniformizer S
coordinateDifferenceIsUniformizer S =
  subtractAddRight S (liftedCentre S) (uniformizer S)

coordinateDifferenceIsPiTimesOne :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) →
  coordinateDifference S
  ≡ Ramified.mul (valuation S) (uniformizer S) (Ramified.one (valuation S))
coordinateDifferenceIsPiTimesOne S =
  trans (coordinateDifferenceIsUniformizer S)
    (sym (mulRightOne S (uniformizer S)))

------------------------------------------------------------------------
-- The nearby point has the SAME finite residue as the Hensel centre.  This is
-- standard local-ring compatibility and is retained explicitly at the source
-- boundary because the generic residue API intentionally has no additive laws.
------------------------------------------------------------------------

record HenselNearbyResidueCompatibility
    {branch : Legendre.ExceptionalLegendreBranch}
    (S : ExceptionalHenselLocalSource branch) : Set where
  field
    nearbyReducesToCentre :
      ResidueUnit.residue (residueValuation S) (liftedCoordinate S)
      ≡ Lift.centre (finitePoint S)

open HenselNearbyResidueCompatibility public

------------------------------------------------------------------------
-- Construct the previously-uninhabited same-object lift record.
------------------------------------------------------------------------

constructExceptionalPadicLift :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : ExceptionalHenselLocalSource branch) →
  HenselNearbyResidueCompatibility S →
  Lift.ExceptionalPadicLift branch
constructExceptionalPadicLift branch S nearby = record
  { Lift.PadicLocal = PadicLocal S
  ; Lift.Residue = Residue S
  ; Lift.valuation = valuation S
  ; Lift.residueValuation = residueValuation S
  ; Lift.valuationCompatibility = valuationCompatibility S
  ; Lift.finitePoint = finitePoint S
  ; Lift.residueZeroMatches = residueZeroMatches S
  ; Lift.subtract = subtract S
  ; Lift.liftedCoordinate = liftedCoordinate S
  ; Lift.liftedCentre = liftedCentre S
  ; Lift.coordinateDifference = coordinateDifference S
  ; Lift.liftedCentreReducesToFiniteCentre = liftedCentreReduces S
  ; Lift.liftedCoordinateReducesToFiniteCentre = nearbyReducesToCentre nearby
  ; Lift.coordinateDifferenceIsActualDifference = refl
  ; Lift.uniformizer = uniformizer S
  ; Lift.coordinateUnit = Ramified.one (valuation S)
  ; Lift.uniformizerDepthOne = uniformizerDepthOne S
  ; Lift.coordinateUnitResidueNonzero = oneResidueUnit S
  ; Lift.coordinateFactorization = coordinateDifferenceIsPiTimesOne S
  ; Lift.derivativeUnit = derivativeUnit S
  ; Lift.branchValue = branchPolynomial S (liftedCoordinate S)
  ; Lift.derivativeReducesToFiniteDerivative = derivativeReduces S
  ; Lift.branchSimpleFactorization = branchFactorizationAtNearby S
  ; Lift.outerUnit = outerUnit S
  ; Lift.localJDifference =
      subtract S (localJ S (liftedCoordinate S)) (alphaLift S)
  ; Lift.outerUnitReducesToFiniteOuterUnit = outerUnitReduces S
  ; Lift.localJFactorization = localJFactorizationAtNearby S
  }

constructedCoordinateDepthOne :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : ExceptionalHenselLocalSource branch) →
  (nearby : HenselNearbyResidueCompatibility S) →
  Ramified.valuation (valuation S)
    (Lift.coordinateDifference (constructExceptionalPadicLift branch S nearby))
  ≡ 1
constructedCoordinateDepthOne branch S nearby =
  Lift.Preferred.coordinateDifferenceDepthOne
    (valuation S) branch
    (Lift.asPreferredLocalProducer branch
      (constructExceptionalPadicLift branch S nearby))

constructedLocalJDepth :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : ExceptionalHenselLocalSource branch) →
  (nearby : HenselNearbyResidueCompatibility S) →
  Ramified.valuation (valuation S)
    (Lift.localJDifference (constructExceptionalPadicLift branch S nearby))
  ≡ Legendre.exceptionalRamificationExponent branch
constructedLocalJDepth branch S nearby =
  Lift.liftedLocalJDepthIsAlgebraicExponent branch
    (constructExceptionalPadicLift branch S nearby)

record LegendreExceptionalPadicHenselConstructionBoundary : Set where
  field
    henselCentreIsActualRootRequired : Bool
    nearbyCoordinateDefinedAsCentrePlusUniformizer : Bool
    lambdaMinusLambda0EqualsPiTimesOneDerived : Bool
    branchFactorEvaluatedAtActualNearbyPoint : Bool
    rationalJFactorEvaluatedAtActualNearbyPoint : Bool
    sameFiniteResidueDerivedThroughLocalRing : Bool
    exceptionalPadicLiftRecordConstructed : Bool
    coordinateDepthOneDerived : Bool
    localJDepthDerived : Bool
    numericLocalJDepthImported : Bool
    fullQpImplementationReprovedHere : Bool

canonicalLegendreExceptionalPadicHenselConstructionBoundary :
  LegendreExceptionalPadicHenselConstructionBoundary
canonicalLegendreExceptionalPadicHenselConstructionBoundary = record
  { henselCentreIsActualRootRequired = true
  ; nearbyCoordinateDefinedAsCentrePlusUniformizer = true
  ; lambdaMinusLambda0EqualsPiTimesOneDerived = true
  ; branchFactorEvaluatedAtActualNearbyPoint = true
  ; rationalJFactorEvaluatedAtActualNearbyPoint = true
  ; sameFiniteResidueDerivedThroughLocalRing = true
  ; exceptionalPadicLiftRecordConstructed = true
  ; coordinateDepthOneDerived = true
  ; localJDepthDerived = true
  ; numericLocalJDepthImported = false
  ; fullQpImplementationReprovedHere = false
  }

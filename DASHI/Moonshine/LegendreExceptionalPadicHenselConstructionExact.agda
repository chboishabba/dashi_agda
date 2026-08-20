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
-- Hensel lifting / complete local-field context and the Legendre family.
--
-- DASHI CONTRIBUTION
--
-- The lifted exceptional centre is no longer chosen as an unrelated p-adic
-- element.  A standard Hensel-lift operation is the source boundary, and
--
--     lambda0 := henselLift finiteCentre
--
-- definitionally.  Its reduction and branch-root law are the ordinary Hensel
-- conclusions.  The nearby point is then DEFINED by
--
--     lambda := lambda0 + pi,
--
-- so lambda-lambda0 = pi*1 is derived.  Residue additivity and residue(pi)=0
-- derive that lambda has the same certified finite residue.  The selected
-- branch quotient and rational J-alpha outer factor are actual local elements
-- evaluated at this SAME lambda.
--
-- This is intentionally an adapter to standard complete-DVR/Hensel authority;
-- it does not reimplement Q_p or Hensel's lemma from Cauchy sequences.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.ResidueDetectedUnitValuationExact as ResidueUnit
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreJExceptionalResidueLocalProducerExact as Preferred
import DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact as Lift

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

    add subtract : PadicLocal → PadicLocal → PadicLocal
    subtractAddRight : (x d : PadicLocal) → subtract (add x d) x ≡ d

    residueAdd : Residue → Residue → Residue
    residueAddHom :
      (x y : PadicLocal) →
      ResidueUnit.residue residueValuation (add x y)
      ≡ residueAdd
          (ResidueUnit.residue residueValuation x)
          (ResidueUnit.residue residueValuation y)
    residueAddZeroRight :
      (r : Residue) →
      residueAdd r (ResidueUnit.residueZero residueValuation) ≡ r

    zeroLocal : PadicLocal
    branchPolynomial : PadicLocal → PadicLocal

    -- STANDARD HENSEL AUTHORITY.  The selected finite centre is not followed by
    -- a separately chosen lift; lambda0 is the output of this operation.
    henselLift : Residue → PadicLocal
    henselLiftReduces :
      (r : Residue) →
      ResidueUnit.residue residueValuation (henselLift r) ≡ r
    henselSelectedCentreIsRoot :
      branchPolynomial (henselLift (Lift.centre finitePoint)) ≡ zeroLocal

    uniformizer : PadicLocal
    uniformizerDepthOne : Ramified.valuation valuation uniformizer ≡ 1
    uniformizerReducesToZero :
      ResidueUnit.residue residueValuation uniformizer
      ≡ ResidueUnit.residueZero residueValuation

    oneResidueUnit :
      ResidueUnit.ResidueUnitWitness residueValuation (Ramified.one valuation)
    mulRightOne :
      (x : PadicLocal) → Ramified.mul valuation x (Ramified.one valuation) ≡ x

    -- ACTUAL simple-factor quotient at lambda=lambda0+pi.
    derivativeUnit : PadicLocal
    derivativeReduces :
      ResidueUnit.residue residueValuation derivativeUnit
      ≡ Lift.derivativeResidue finitePoint
    branchFactorizationAtNearby :
      branchPolynomial
        (add (henselLift (Lift.centre finitePoint)) uniformizer)
      ≡ Ramified.mul valuation
          (subtract
            (add (henselLift (Lift.centre finitePoint)) uniformizer)
            (henselLift (Lift.centre finitePoint)))
          derivativeUnit

    -- ACTUAL rational-function J-alpha factor at the SAME nearby point.
    alphaLift : PadicLocal
    localJ : PadicLocal → PadicLocal
    outerUnit : PadicLocal
    outerUnitReduces :
      ResidueUnit.residue residueValuation outerUnit
      ≡ Lift.outerUnitResidue finitePoint
    localJFactorizationAtNearby :
      subtract
        (localJ (add (henselLift (Lift.centre finitePoint)) uniformizer))
        alphaLift
      ≡ Ramified.mul valuation outerUnit
          (Ramified.pow valuation
            (branchPolynomial
              (add (henselLift (Lift.centre finitePoint)) uniformizer))
            (Legendre.exceptionalRamificationExponent branch))

open ExceptionalHenselLocalSource public

liftedCentre :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) → PadicLocal S
liftedCentre S = henselLift S (Lift.centre (finitePoint S))

liftedCentreReducesToFiniteCentre :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) →
  ResidueUnit.residue (residueValuation S) (liftedCentre S)
  ≡ Lift.centre (finitePoint S)
liftedCentreReducesToFiniteCentre S =
  henselLiftReduces S (Lift.centre (finitePoint S))

liftedCentreIsActualBranchRoot :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) →
  branchPolynomial S (liftedCentre S) ≡ zeroLocal S
liftedCentreIsActualBranchRoot S = henselSelectedCentreIsRoot S

liftedCoordinate :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) → PadicLocal S
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

liftedCoordinateReducesToLiftedCentre :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) →
  ResidueUnit.residue (residueValuation S) (liftedCoordinate S)
  ≡ ResidueUnit.residue (residueValuation S) (liftedCentre S)
liftedCoordinateReducesToLiftedCentre S =
  trans
    (residueAddHom S (liftedCentre S) (uniformizer S))
    (trans
      (cong
        (λ r → residueAdd S
          (ResidueUnit.residue (residueValuation S) (liftedCentre S)) r)
        (uniformizerReducesToZero S))
      (residueAddZeroRight S
        (ResidueUnit.residue (residueValuation S) (liftedCentre S))))

liftedCoordinateReducesToFiniteCentre :
  {branch : Legendre.ExceptionalLegendreBranch} →
  (S : ExceptionalHenselLocalSource branch) →
  ResidueUnit.residue (residueValuation S) (liftedCoordinate S)
  ≡ Lift.centre (finitePoint S)
liftedCoordinateReducesToFiniteCentre S =
  trans
    (liftedCoordinateReducesToLiftedCentre S)
    (liftedCentreReducesToFiniteCentre S)

constructExceptionalPadicLift :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : ExceptionalHenselLocalSource branch) →
  Lift.ExceptionalPadicLift branch
constructExceptionalPadicLift branch S = record
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
  ; Lift.liftedCentreReducesToFiniteCentre = liftedCentreReducesToFiniteCentre S
  ; Lift.liftedCoordinateReducesToFiniteCentre = liftedCoordinateReducesToFiniteCentre S
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
  Ramified.valuation (valuation S)
    (Lift.coordinateDifference (constructExceptionalPadicLift branch S)) ≡ 1
constructedCoordinateDepthOne branch S =
  Preferred.coordinateDifferenceDepthOne
    (valuation S) branch
    (Lift.asPreferredLocalProducer branch (constructExceptionalPadicLift branch S))

constructedLocalJDepth :
  (branch : Legendre.ExceptionalLegendreBranch) →
  (S : ExceptionalHenselLocalSource branch) →
  Ramified.valuation (valuation S)
    (Lift.localJDifference (constructExceptionalPadicLift branch S))
  ≡ Legendre.exceptionalRamificationExponent branch
constructedLocalJDepth branch S =
  Lift.liftedLocalJDepthIsAlgebraicExponent branch
    (constructExceptionalPadicLift branch S)

record LegendreExceptionalPadicHenselConstructionBoundary : Set where
  field
    henselLiftOperationIsSourceBoundary : Bool
    liftedCentreDefinedFromFiniteCentre : Bool
    liftedCentreRootLawRequired : Bool
    nearbyCoordinateDefinedAsCentrePlusUniformizer : Bool
    lambdaMinusLambda0EqualsPiTimesOneDerived : Bool
    nearbyResidueDerivedFromResidueHomomorphism : Bool
    branchFactorEvaluatedAtActualNearbyPoint : Bool
    rationalJFactorEvaluatedAtActualNearbyPoint : Bool
    exceptionalPadicLiftRecordConstructed : Bool
    coordinateDepthOneDerived : Bool
    localJDepthDerived : Bool
    numericLocalJDepthImported : Bool
    fullQpImplementationReprovedHere : Bool

canonicalLegendreExceptionalPadicHenselConstructionBoundary :
  LegendreExceptionalPadicHenselConstructionBoundary
canonicalLegendreExceptionalPadicHenselConstructionBoundary = record
  { henselLiftOperationIsSourceBoundary = true
  ; liftedCentreDefinedFromFiniteCentre = true
  ; liftedCentreRootLawRequired = true
  ; nearbyCoordinateDefinedAsCentrePlusUniformizer = true
  ; lambdaMinusLambda0EqualsPiTimesOneDerived = true
  ; nearbyResidueDerivedFromResidueHomomorphism = true
  ; branchFactorEvaluatedAtActualNearbyPoint = true
  ; rationalJFactorEvaluatedAtActualNearbyPoint = true
  ; exceptionalPadicLiftRecordConstructed = true
  ; coordinateDepthOneDerived = true
  ; localJDepthDerived = true
  ; numericLocalJDepthImported = false
  ; fullQpImplementationReprovedHere = false
  }

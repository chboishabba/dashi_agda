module DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Round 38 proved that the raw ordered physical-incidence fold cancels on the
-- exact rational carrier.  The remaining F4 seam was to identify that fold
-- with the *actual projected Galerkin convection/energy pairing*.  The
-- repository already defines projected nonlinearity output-by-output as the
-- sum over the literal `physicalOutputFiber`.
--
-- This module closes that same-object equality at each output mode. Hermitian
-- pairing and real part are distributed through the actual vector sum, and
-- output-fibre soundness rewrites the test mode `k(tau)` to the selected
-- output. Thus
--
--   Re <u_k, projectedNonlinearity_k>
--     = sum_{tau : k(tau)=k} OrderedPower(tau).
--
-- No symmetrized coefficient, orbit cardinality, or hidden factor two occurs.
-- The remaining global F4 step is only the finite partition of the complete
-- triad enumeration by the literal output-mode list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38

F : C3.RealField _
F = Rational.rationalRealField

realHermitianPower : C3.Complex3 F → C3.Complex3 F → ℚ
realHermitianPower test value =
  C3.real (C3.complexRealPart (C3.hermitianPairing3 test value))

hermitianZeroRight :
  (test : C3.Complex3 F) →
  C3.hermitianPairing3 test (C3.complex3Zero F)
  ≡ C3.complexZero F
hermitianZeroRight (C3.complex3 tx ty tz) =
  trans
    (cong
      (λ first →
        C3.complexAdd first
          (C3.complexMultiply (C3.complexConjugate tz) (C3.complexZero F)))
      (cong₂ C3.complexAdd
        (Algebra.complexMultiplyZeroRight (C3.complexConjugate tx))
        (Algebra.complexMultiplyZeroRight (C3.complexConjugate ty))))
    (trans
      (cong
        (λ last →
          C3.complexAdd
            (C3.complexAdd (C3.complexZero F) (C3.complexZero F)) last)
        (Algebra.complexMultiplyZeroRight (C3.complexConjugate tz)))
      (trans
        (cong
          (λ first → C3.complexAdd first (C3.complexZero F))
          (Algebra.complexAddZeroLeft (C3.complexZero F)))
        (Algebra.complexAddZeroRight (C3.complexZero F))))

realHermitianPowerZeroRight :
  (test : C3.Complex3 F) →
  realHermitianPower test (C3.complex3Zero F) ≡ 0ℚ
realHermitianPowerZeroRight test =
  trans
    (cong
      (λ paired → C3.real (C3.complexRealPart paired))
      (hermitianZeroRight test))
    refl

realHermitianPowerAddRight :
  (test left right : C3.Complex3 F) →
  realHermitianPower test (C3.complex3Add left right)
  ≡ realHermitianPower test left + realHermitianPower test right
realHermitianPowerAddRight test left right =
  trans
    (cong
      (λ paired → C3.real (C3.complexRealPart paired))
      (Algebra.hermitianAddRight test left right))
    (trans
      (cong C3.real
        (Algebra.complexRealPartAdd
          (C3.hermitianPairing3 test left)
          (C3.hermitianPairing3 test right)))
      refl)

projectedTermPowerAtOutput :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode →
  Physical.PhysicalTriadIncidence → ℚ
projectedTermPowerAtOutput system output tau =
  realHermitianPower
    (Equation.velocity system output)
    (Equation.projectedOrderedTerm system tau)

sumOutputTermPowers :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode →
  List Physical.PhysicalTriadIncidence → ℚ
sumOutputTermPowers system output [] = 0ℚ
sumOutputTermPowers system output (tau ∷ rest) =
  projectedTermPowerAtOutput system output tau
  + sumOutputTermPowers system output rest

pairingWithVectorSumIsTermPowerSum :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  (triads : List Physical.PhysicalTriadIncidence) →
  realHermitianPower
    (Equation.velocity system output)
    (Equation.sumVectors (Equation.mapTriadTerms system triads))
  ≡ sumOutputTermPowers system output triads
pairingWithVectorSumIsTermPowerSum system output [] =
  realHermitianPowerZeroRight (Equation.velocity system output)
pairingWithVectorSumIsTermPowerSum system output (tau ∷ rest) =
  trans
    (realHermitianPowerAddRight
      (Equation.velocity system output)
      (Equation.projectedOrderedTerm system tau)
      (Equation.sumVectors (Equation.mapTriadTerms system rest)))
    (cong
      (projectedTermPowerAtOutput system output tau +_)
      (pairingWithVectorSumIsTermPowerSum system output rest))

outputFiberTermPowerIsOrderedPower :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  (tau : Physical.PhysicalTriadIncidence) →
  Cube._∈_ tau (Equation.concreteTriadsAt system output) →
  projectedTermPowerAtOutput system output tau
  ≡ Round38.orderedPower E I tau (Equation.velocity system)
outputFiberTermPowerIsOrderedPower {E} {I} system output tau member =
  let
    outputMeaning : Physical.k tau ≡ output
    outputMeaning = Equation.concreteTriadsAtOutputAgreement member
  in
  subst
    (λ selectedOutput →
      projectedTermPowerAtOutput system selectedOutput tau
      ≡ Round38.orderedPower E I tau (Equation.velocity system))
    outputMeaning
    refl

sumOutputFiberPowersIsOrderedFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  sumOutputTermPowers system output (Equation.concreteTriadsAt system output)
  ≡
  Round38.foldPower
    (λ tau → Round38.orderedPower E I tau (Equation.velocity system))
    (Equation.concreteTriadsAt system output)
sumOutputFiberPowersIsOrderedFold {E} {I} system output =
  go
    (Equation.concreteTriadsAt system output)
    (λ tau member → outputFiberTermPowerIsOrderedPower system output tau member)
  where
  go :
    (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items →
      projectedTermPowerAtOutput system output tau
      ≡ Round38.orderedPower E I tau (Equation.velocity system)) →
    sumOutputTermPowers system output items
    ≡ Round38.foldPower
        (λ tau → Round38.orderedPower E I tau (Equation.velocity system))
        items
  go [] pointwise = refl
  go (tau ∷ rest) pointwise =
    cong₂ _+_
      (pointwise tau (Cube.here refl))
      (go rest (λ selected member →
        pointwise selected (Cube.there member)))

projectedOutputEnergyPairingEqualsOrderedFiberFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  realHermitianPower
    (Equation.velocity system output)
    (Equation.projectedNonlinearity system output)
  ≡
  Round38.foldPower
    (λ tau → Round38.orderedPower E I tau (Equation.velocity system))
    (Equation.concreteTriadsAt system output)
projectedOutputEnergyPairingEqualsOrderedFiberFold system output =
  trans
    (pairingWithVectorSumIsTermPowerSum
      system output (Equation.concreteTriadsAt system output))
    (sumOutputFiberPowersIsOrderedFold system output)

f4ProjectedOutputPairingClosed : Bool
f4ProjectedOutputPairingClosed = true

literalGlobalModeFiberPartitionConstructed : Bool
literalGlobalModeFiberPartitionConstructed = false

f4ProjectedOutputPairingClosedIsTrue :
  f4ProjectedOutputPairingClosed ≡ true
f4ProjectedOutputPairingClosedIsTrue = refl

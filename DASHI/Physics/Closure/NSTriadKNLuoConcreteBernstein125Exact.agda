module DASHI.Physics.Closure.NSTriadKNLuoConcreteBernstein125Exact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Specialize the finite Fourier-coefficient Bernstein producer to the exact
-- five-by-five-by-five base enumeration. The fully concrete theorem gives
--
--   outputL2Squared <= 125 * 8^q * inputL1Squared
--
-- uniformly in every Galerkin cutoff included in the Boolean shell predicate,
-- with no separate base-mass producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicBernsteinRealizationExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact as Fourier
import DASHI.Physics.Closure.NSTriadKNLuoConcreteDyadicSupportCount125Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNLuoConcreteIntegerCube125EnumerationExact as Cube
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

record ConcreteBernstein125Data (Slot : Set) : Set₁ where
  constructor concrete-bernstein-125-data
  field
    bernsteinData : Bernstein.DyadicBernsteinRealization Slot
    baseMassBound :
      Support.countMass (Bernstein.baseEnumeration bernsteinData)
      ≤ Concrete.oneTwentyFive

open ConcreteBernstein125Data public

concreteBernstein125Square :
  ∀ {Slot : Set}
    (dataSet : ConcreteBernstein125Data Slot) →
  Bernstein.outputL2Squared (bernsteinData dataSet)
  ≤ (Concrete.oneTwentyFive
      * Geo.pow Support.eight
          (Bernstein.shell (bernsteinData dataSet)))
    * Bernstein.commonInputL1Squared (bernsteinData dataSet)
concreteBernstein125Square dataSet =
  let
    base = Bernstein.finiteDyadicBernsteinSquare (bernsteinData dataSet)

    powerNN :
      0ℚ ≤ Geo.pow Support.eight
        (Bernstein.shell (bernsteinData dataSet))
    powerNN =
      Geo.powNonnegative
        Support.eight
        (Bernstein.shell (bernsteinData dataSet))
        Concrete.eightNonnegative

    scaleBound :
      Geo.pow Support.eight (Bernstein.shell (bernsteinData dataSet))
        * Support.countMass (Bernstein.baseEnumeration (bernsteinData dataSet))
      ≤ Geo.pow Support.eight (Bernstein.shell (bernsteinData dataSet))
        * Concrete.oneTwentyFive
    scaleBound =
      let instance powerNNI = nonNegative powerNN
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Geo.pow Support.eight (Bernstein.shell (bernsteinData dataSet)))
        (baseMassBound dataSet)

    inputNN =
      Bernstein.commonInputL1SquaredNonnegative (bernsteinData dataSet)

    finalScale :
      Bernstein.outputScaleCubed (bernsteinData dataSet)
        * Bernstein.commonInputL1Squared (bernsteinData dataSet)
      ≤ (Concrete.oneTwentyFive
          * Geo.pow Support.eight
              (Bernstein.shell (bernsteinData dataSet)))
        * Bernstein.commonInputL1Squared (bernsteinData dataSet)
    finalScale =
      let
        reordered :
          Geo.pow Support.eight (Bernstein.shell (bernsteinData dataSet))
            * Concrete.oneTwentyFive
          ≡ Concrete.oneTwentyFive
            * Geo.pow Support.eight (Bernstein.shell (bernsteinData dataSet))
        reordered =
          ℚₚ.*-comm
            (Geo.pow Support.eight (Bernstein.shell (bernsteinData dataSet)))
            Concrete.oneTwentyFive

        scaled =
          let instance inputNNI = nonNegative inputNN
          in
          ℚₚ.*-monoʳ-≤-nonNeg
            (Bernstein.commonInputL1Squared (bernsteinData dataSet))
            scaleBound
      in
      subst
        (λ upper →
          Bernstein.outputScaleCubed (bernsteinData dataSet)
            * Bernstein.commonInputL1Squared (bernsteinData dataSet)
          ≤ upper
            * Bernstein.commonInputL1Squared (bernsteinData dataSet))
        reordered
        scaled
  in
  ℚₚ.≤-trans base finalScale

record FullyConcreteBernstein125Data : Set where
  constructor fully-concrete-bernstein-125-data
  field
    shell125 : Nat
    shellPredicate125 : Cube.Cube125 → Bool
    commonInputL1Squared125 : ℚ
    commonInputL1Squared125Nonnegative :
      0ℚ ≤ commonInputL1Squared125
    coefficientData125 :
      Cube.Cube125 → Fourier.FiniteFourierCoefficientData
    commonInputMeaning125 :
      (slot : Cube.Cube125) →
      Fourier.inputL1Squared (coefficientData125 slot)
      ≡ commonInputL1Squared125

open FullyConcreteBernstein125Data public

fullyConcreteBernsteinData :
  FullyConcreteBernstein125Data →
  Bernstein.DyadicBernsteinRealization Cube.Cube125
fullyConcreteBernsteinData dataSet =
  Bernstein.dyadic-bernstein-realization
    Cube.cube125
    (shell125 dataSet)
    (shellPredicate125 dataSet)
    (commonInputL1Squared125 dataSet)
    (commonInputL1Squared125Nonnegative dataSet)
    (coefficientData125 dataSet)
    (commonInputMeaning125 dataSet)

fullyConcreteBernstein125Data :
  FullyConcreteBernstein125Data →
  ConcreteBernstein125Data Cube.Cube125
fullyConcreteBernstein125Data dataSet =
  concrete-bernstein-125-data
    (fullyConcreteBernsteinData dataSet)
    Concrete.cube125MassBound

fullyConcreteBernstein125Square :
  (dataSet : FullyConcreteBernstein125Data) →
  Bernstein.outputL2Squared (fullyConcreteBernsteinData dataSet)
  ≤ (Concrete.oneTwentyFive
      * Geo.pow Support.eight (shell125 dataSet))
    * commonInputL1Squared125 dataSet
fullyConcreteBernstein125Square dataSet =
  concreteBernstein125Square
    (fullyConcreteBernstein125Data dataSet)

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
-- Specialize the finite Fourier-coefficient Bernstein producer to the
-- concrete integer-cube support constant. If the base enumeration has mass at
-- most 125, then
--
--   outputL2Squared <= 125 * 8^q * inputL1Squared.
--
-- The estimate is uniform in every Galerkin cutoff included in the Boolean
-- shell predicate.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicBernsteinRealizationExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNLuoConcreteDyadicSupportCount125Exact as Concrete
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

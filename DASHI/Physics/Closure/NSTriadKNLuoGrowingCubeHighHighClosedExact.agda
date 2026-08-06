module DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeHighHighClosedExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
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
-- Put the exact Leray/H^-1 multiplier cancellation on the growing finite cube
-- and compose it with the concrete support-count Bernstein theorem:
--
--   sum_(k in S_q) |k|^-2 |P(k)(ik . Fhat(k))|^2
--     <= 125 * 8^q * ||F||_1^2.
--
-- No repeated base enumeration, support-count field, or multiplier-contraction
-- field remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoGrowingFiniteCubeSupportExact as Growing
import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeBernsteinExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact as Fourier
import DASHI.Physics.Closure.NSTriadKNLuoRationalLerayMultiplierContractiveExact as Leray
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity

record GrowingCubeHighHighData (shell : Nat) : Set₁ where
  constructor growing-cube-high-high-data
  field
    bernsteinData : Bernstein.GrowingCubeBernsteinData shell
    lerayModeData :
      Growing.ModeAt shell → Leray.ComplexProjectedDivergenceData

    tensorCoefficientMeaning :
      (mode : Growing.ModeAt shell) →
      Leray.complexMatrixNormSquared
        (Leray.complexTensor (lerayModeData mode))
      ≡ Fourier.coefficientSquared
        (Bernstein.coefficientData bernsteinData mode)

open GrowingCubeHighHighData public

hMinusOneSquaredAt :
  ∀ {shell : Nat} →
  GrowingCubeHighHighData shell →
  Growing.ModeAt shell → ℚ
hMinusOneSquaredAt dataSet mode =
  Leray.complexHMinusOneSquared (lerayModeData dataSet mode)

finiteHMinusOneSquared :
  (shell : Nat) →
  GrowingCubeHighHighData shell → ℚ
finiteHMinusOneSquared shell dataSet =
  Bernstein.sumBy
    (Bernstein.retainedModes shell (bernsteinData dataSet))
    (hMinusOneSquaredAt dataSet)

modeHMinusOneByCoefficient :
  ∀ {shell : Nat}
    (dataSet : GrowingCubeHighHighData shell)
    (mode : Growing.ModeAt shell) →
  hMinusOneSquaredAt dataSet mode
  ≤ Bernstein.coefficientSquaredAt (bernsteinData dataSet) mode
modeHMinusOneByCoefficient dataSet mode =
  subst
    (λ upper → hMinusOneSquaredAt dataSet mode ≤ upper)
    (tensorCoefficientMeaning dataSet mode)
    (Leray.complexHMinusOneCancellation
      (lerayModeData dataSet mode))

sumHMinusOneByCoefficients :
  ∀ {shell : Nat}
    (dataSet : GrowingCubeHighHighData shell)
    (modes : List (Growing.ModeAt shell)) →
  Bernstein.sumBy modes (hMinusOneSquaredAt dataSet)
  ≤ Bernstein.sumBy modes
      (Bernstein.coefficientSquaredAt (bernsteinData dataSet))
sumHMinusOneByCoefficients dataSet [] = ℚₚ.≤-refl
sumHMinusOneByCoefficients dataSet (mode ∷ modes) =
  ℚₚ.+-mono-≤
    (modeHMinusOneByCoefficient dataSet mode)
    (sumHMinusOneByCoefficients dataSet modes)

growingCubeHighHighSquareBound :
  (shell : Nat) →
  (dataSet : GrowingCubeHighHighData shell) →
  finiteHMinusOneSquared shell dataSet
  ≤ (Capacity.oneTwentyFive * Capacity.eightPower shell)
    * Bernstein.commonInputL1Squared (bernsteinData dataSet)
growingCubeHighHighSquareBound shell dataSet =
  ℚₚ.≤-trans
    (sumHMinusOneByCoefficients
      dataSet
      (Bernstein.retainedModes shell (bernsteinData dataSet)))
    (Bernstein.growingCubeBernsteinSquare
      shell
      (bernsteinData dataSet))

module DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusHighHighExact where

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
-- Specialize the growing-cube Leray/H^-1 and tensor-Holder chain to the
-- explicit dyadic annulus intersected with a Galerkin cutoff.  The final
-- finite producer is
--
--   HMinusOneSquared(q,N)
--     <= 125 * 8^q * leftL2Squared * rightL2Squared.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoGrowingFiniteCubeSupportExact as Growing
import DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusBernsteinExact as Annular
import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeHighHighClosedExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeHighHighTensorClosedExact as HHTensor
import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeBernsteinExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact as Fourier
import DASHI.Physics.Closure.NSTriadKNLuoRationalLerayMultiplierContractiveExact as Leray
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTensorHolderExact as Tensor
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity

record AnnularHighHighData (shell : Nat) : Set₁ where
  constructor annular-high-high-data
  field
    annularBernsteinData : Annular.AnnularGalerkinBernsteinData shell
    lerayModeData :
      Growing.ModeAt shell → Leray.ComplexProjectedDivergenceData
    tensorCoefficientMeaning :
      (mode : Growing.ModeAt shell) →
      Leray.complexMatrixNormSquared
        (Leray.complexTensor (lerayModeData mode))
      ≡ Fourier.coefficientSquared
        (Annular.coefficientData annularBernsteinData mode)

open AnnularHighHighData public

asGrowingHighHighData :
  ∀ {shell : Nat} →
  AnnularHighHighData shell →
  HH.GrowingCubeHighHighData shell
asGrowingHighHighData dataSet =
  HH.growing-cube-high-high-data
    (Annular.asGrowingBernsteinData
      (annularBernsteinData dataSet))
    (lerayModeData dataSet)
    (tensorCoefficientMeaning dataSet)

annularHighHighHMinusOneSquared :
  (shell : Nat) →
  AnnularHighHighData shell → ℚ
annularHighHighHMinusOneSquared shell dataSet =
  HH.finiteHMinusOneSquared shell (asGrowingHighHighData dataSet)

annularHighHighSquareBound :
  (shell : Nat) →
  (dataSet : AnnularHighHighData shell) →
  annularHighHighHMinusOneSquared shell dataSet
  ≤ (Capacity.oneTwentyFive * Capacity.eightPower shell)
    * Annular.commonInputL1Squared (annularBernsteinData dataSet)
annularHighHighSquareBound shell dataSet =
  HH.growingCubeHighHighSquareBound
    shell
    (asGrowingHighHighData dataSet)

record AnnularHighHighTensorData (shell : Nat) : Set₁ where
  constructor annular-high-high-tensor-data
  field
    annularHighHighData : AnnularHighHighData shell
    tensorData : Tensor.FiniteTensorHolderData
    tensorInputMeaning :
      Annular.commonInputL1Squared
        (annularBernsteinData annularHighHighData)
      ≡ Tensor.tensorL1Squared tensorData

open AnnularHighHighTensorData public

asGrowingHighHighTensorData :
  ∀ {shell : Nat} →
  AnnularHighHighTensorData shell →
  HHTensor.GrowingCubeHighHighTensorData shell
asGrowingHighHighTensorData dataSet =
  HHTensor.growing-cube-high-high-tensor-data
    (asGrowingHighHighData (annularHighHighData dataSet))
    (tensorData dataSet)
    (tensorInputMeaning dataSet)

annularHighHighTensorSquareBound :
  (shell : Nat) →
  (dataSet : AnnularHighHighTensorData shell) →
  annularHighHighHMinusOneSquared
    shell
    (annularHighHighData dataSet)
  ≤ (Capacity.oneTwentyFive * Capacity.eightPower shell)
    * (Tensor.leftL2Squared (tensorData dataSet)
      * Tensor.rightL2Squared (tensorData dataSet))
annularHighHighTensorSquareBound shell dataSet =
  HHTensor.growingCubeHighHighTensorSquareBound
    shell
    (asGrowingHighHighTensorData dataSet)

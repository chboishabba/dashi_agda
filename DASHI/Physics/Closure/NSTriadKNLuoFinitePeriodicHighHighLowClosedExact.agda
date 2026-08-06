module DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicHighHighLowClosedExact where

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
-- Close the finite periodic HH1 producer without leaving tensor Holder as an
-- assumption.  The module combines:
--
-- * modewise H^{-1}/derivative cancellation and Leray contraction;
-- * finite lattice-support Bernstein;
-- * the repository's Gram-defect proof of finite Cauchy--Schwarz.
--
-- The only remaining continuum obligations are the exact Fourier coefficient
-- identifications and the lattice support-count certificate supplied as
-- fields of the imported finite carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicLerayDivergenceExact as Leray
import DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicBernsteinSupportExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicHighHighLowProducerExact as Producer
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTensorHolderExact as Tensor

record ClosedPeriodicHighHighLowData : Set₁ where
  constructor closed-periodic-high-high-low-data
  field
    lerayModes : List Leray.PeriodicLerayMode
    bernsteinData : Bernstein.FinitePeriodicBernsteinData
    tensorData : Tensor.FiniteTensorHolderData

    outputScaleCubedNonnegative :
      0ℚ ≤ Bernstein.outputScaleCubed bernsteinData

    parsevalBridge :
      Leray.sumTensorModeSquared lerayModes
      ≡ Bernstein.outputL2Squared (Bernstein.modes bernsteinData)

    tensorFourierBridge :
      Bernstein.inputL1Squared bernsteinData
      ≡ Tensor.tensorL1Squared tensorData

open ClosedPeriodicHighHighLowData public

closedProducerData :
  ClosedPeriodicHighHighLowData →
  Producer.PeriodicHighHighLowProducerData
closedProducerData dataSet =
  Producer.periodic-high-high-low-producer-data
    (lerayModes dataSet)
    (bernsteinData dataSet)
    (Tensor.leftL2Squared (tensorData dataSet))
    (Tensor.rightL2Squared (tensorData dataSet))
    (outputScaleCubedNonnegative dataSet)
    (parsevalBridge dataSet)
    tensorBound
  where
  tensorBound :
    Bernstein.inputL1Squared (bernsteinData dataSet)
    ≤ Tensor.leftL2Squared (tensorData dataSet)
      * Tensor.rightL2Squared (tensorData dataSet)
  tensorBound =
    subst
      (λ lower →
        lower
        ≤ Tensor.leftL2Squared (tensorData dataSet)
          * Tensor.rightL2Squared (tensorData dataSet))
      (sym (tensorFourierBridge dataSet))
      (Tensor.finiteTensorHolderSquare (tensorData dataSet))

closedPeriodicHighHighLowSquareBound :
  (dataSet : ClosedPeriodicHighHighLowData) →
  Leray.sumHMinusOneSquared (lerayModes dataSet)
  ≤ Bernstein.outputScaleCubed (bernsteinData dataSet)
      * (Tensor.leftL2Squared (tensorData dataSet)
        * Tensor.rightL2Squared (tensorData dataSet))
closedPeriodicHighHighLowSquareBound dataSet =
  Producer.periodicHighHighLowSquareBound (closedProducerData dataSet)

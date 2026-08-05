module DASHI.Physics.Closure.NSTriadKNCherevanFiniteConvolutionSupportLossExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Source under audit:
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- Harmonic-analysis reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Expose the missing support factor in the paper's repeated use of a
-- "standard bilinear Cauchy--Schwarz estimate on the convolution" as though
-- unnormalised convolution mapped L2 x L2 to L2 with a support-independent
-- constant.
--
-- On a finite group with n points, two constant unit inputs have squared L2
-- masses n and n.  Their unnormalised convolution is the constant n, with
-- squared L2 mass n^3.  Thus
--
--   ||f*g||_2^2 = n (||f||_2^2 ||g||_2^2).
--
-- The exact n=64 witness requires a squared support factor 64.  The continuum
-- analogue must pay a Fourier-support volume, use an L1 factor, or invoke a
-- genuine bilinear multiplier theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _<_)
open import Data.Rational.Properties as ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

constantInputSquaredMass : ℚ → ℚ
constantInputSquaredMass cardinality = cardinality

pairInputSquaredMassProduct : ℚ → ℚ
pairInputSquaredMassProduct cardinality =
  constantInputSquaredMass cardinality
  * constantInputSquaredMass cardinality

constantConvolutionSquaredMass : ℚ → ℚ
constantConvolutionSquaredMass cardinality =
  cardinality * cardinality * cardinality

supportFactorIdentity :
  (cardinality : ℚ) →
  constantConvolutionSquaredMass cardinality
  ≡ cardinality * pairInputSquaredMassProduct cardinality
supportFactorIdentity cardinality = solve (cardinality ∷ [])

sixtyFour : ℚ
sixtyFour = Int.+ 64 / 1

inputProductAtSixtyFour :
  pairInputSquaredMassProduct sixtyFour ≡ Int.+ 4096 / 1
inputProductAtSixtyFour = solve []

outputMassAtSixtyFour :
  constantConvolutionSquaredMass sixtyFour ≡ Int.+ 262144 / 1
outputMassAtSixtyFour = solve []

supportIndependentUnitBoundFails :
  pairInputSquaredMassProduct sixtyFour
  < constantConvolutionSquaredMass sixtyFour
supportIndependentUnitBoundFails =
  toWitness
    {a? = pairInputSquaredMassProduct sixtyFour
       ℚₚ.<? constantConvolutionSquaredMass sixtyFour}
    _

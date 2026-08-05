module DASHI.Physics.Closure.NSTriadKNLuoFiniteTransportCommutatorIdentityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the exact finite kernel identity behind the low--high transport
-- commutator.  For samples indexed by kernel displacements,
--
--   K(a g) - a(0) K(g)
--     = sum_y w_y (a(y)-a(0)) g(y).
--
-- No norm estimate is assumed.  The theorem exposes the unique increment
-- that can pay an inverse frequency after a Littlewood--Paley moment bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record TransportKernelSample : Set where
  constructor transport-kernel-sample
  field
    weight shiftedTransport shiftedDerivative : ℚ

open TransportKernelSample public

kernelProduct : List TransportKernelSample → ℚ
kernelProduct [] = 0ℚ
kernelProduct (sample ∷ samples) =
  weight sample * shiftedTransport sample * shiftedDerivative sample
  + kernelProduct samples

kernelDerivative : List TransportKernelSample → ℚ
kernelDerivative [] = 0ℚ
kernelDerivative (sample ∷ samples) =
  weight sample * shiftedDerivative sample
  + kernelDerivative samples

transportCommutator : ℚ → List TransportKernelSample → ℚ
transportCommutator centerTransport samples =
  kernelProduct samples - centerTransport * kernelDerivative samples

incrementContribution :
  ℚ → TransportKernelSample → ℚ
incrementContribution centerTransport sample =
  weight sample
  * (shiftedTransport sample - centerTransport)
  * shiftedDerivative sample

sumIncrementContributions :
  ℚ → List TransportKernelSample → ℚ
sumIncrementContributions centerTransport [] = 0ℚ
sumIncrementContributions centerTransport (sample ∷ samples) =
  incrementContribution centerTransport sample
  + sumIncrementContributions centerTransport samples

finiteTransportCommutatorIdentity :
  (centerTransport : ℚ) →
  (samples : List TransportKernelSample) →
  transportCommutator centerTransport samples
  ≡ sumIncrementContributions centerTransport samples
finiteTransportCommutatorIdentity centerTransport [] =
  solve (centerTransport ∷ [])
finiteTransportCommutatorIdentity centerTransport (sample ∷ samples) =
  trans
    (commutatorCons centerTransport sample samples)
    (cong
      (incrementContribution centerTransport sample +_)
      (finiteTransportCommutatorIdentity centerTransport samples))
  where
  commutatorCons :
    (center : ℚ) →
    (headSample : TransportKernelSample) →
    (tailSamples : List TransportKernelSample) →
    transportCommutator center (headSample ∷ tailSamples)
    ≡ incrementContribution center headSample
      + transportCommutator center tailSamples
  commutatorCons center headSample tailSamples =
    solve
      ( weight headSample
      ∷ shiftedTransport headSample
      ∷ shiftedDerivative headSample
      ∷ center
      ∷ kernelProduct tailSamples
      ∷ kernelDerivative tailSamples
      ∷ [])

module DASHI.Physics.Closure.NSTriadKNLuoProjectionLeakageCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato and Gustavo Ponce,
-- "Commutator Estimates and the Euler and Navier--Stokes Equations",
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Piero D'Ancona,
-- "A Short Proof of Commutator Estimates", Journal of Fourier Analysis and
-- Applications 25 (2019), 1134--1142.
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- Fabian Waleffe,
-- "The Nature of Triad Interactions in Homogeneous Turbulence",
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- DASHI CONTRIBUTION
--
-- Make the cross-pollination with the RG/Feshbach lane executable rather than
-- terminological.  Every scalar sample in the existing transport commutator
-- is represented as the retained component of a projection commutator on a
-- two-sector block operator.  Summing the samples recovers the complete
-- finite transport commutator exactly.
--
-- The helical sign pair is also represented as a genuine opposite-orientation
-- eigenvalue pair.  This does not construct the continuum helical basis or
-- prove any Navier--Stokes regularity estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Common.FiniteProjectionOffDiagonalExact as Projection
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTransportCommutatorIdentityExact as Transport

sampleLeakageOperator :
  ℚ → Transport.TransportKernelSample → Projection.BlockOperator
sampleLeakageOperator center sample =
  Projection.blockOperator
    0ℚ
    (Transport.weight sample
      * (Transport.shiftedTransport sample - center))
    0ℚ
    0ℚ

sampleLeakageVector :
  Transport.TransportKernelSample → Projection.SectorVector
sampleLeakageVector sample =
  Projection.sectorVector 0ℚ (Transport.shiftedDerivative sample)

sampleIncrementIsRetainedProjectionLeakage :
  (center : ℚ) →
  (sample : Transport.TransportKernelSample) →
  Projection.retained
    (Projection.projectionCommutator
      (sampleLeakageOperator center sample)
      (sampleLeakageVector sample))
  ≡ Transport.incrementContribution center sample
sampleIncrementIsRetainedProjectionLeakage center sample =
  ℚRing.solve-∀
    (Transport.weight sample)
    (Transport.shiftedTransport sample)
    center
    (Transport.shiftedDerivative sample)

sumProjectionLeakages :
  ℚ → List Transport.TransportKernelSample → ℚ
sumProjectionLeakages center [] = 0ℚ
sumProjectionLeakages center (sample ∷ samples) =
  Projection.retained
    (Projection.projectionCommutator
      (sampleLeakageOperator center sample)
      (sampleLeakageVector sample))
  + sumProjectionLeakages center samples

sumIncrementsAreProjectionLeakages :
  (center : ℚ) →
  (samples : List Transport.TransportKernelSample) →
  Transport.sumIncrementContributions center samples
  ≡ sumProjectionLeakages center samples
sumIncrementsAreProjectionLeakages center [] = refl
sumIncrementsAreProjectionLeakages center (sample ∷ samples) =
  cong₂ _+_
    (sym (sampleIncrementIsRetainedProjectionLeakage center sample))
    (sumIncrementsAreProjectionLeakages center samples)

transportCommutatorIsProjectionLeakage :
  (center : ℚ) →
  (samples : List Transport.TransportKernelSample) →
  Transport.transportCommutator center samples
  ≡ sumProjectionLeakages center samples
transportCommutatorIsProjectionLeakage center samples =
  trans
    (Transport.finiteTransportCommutatorIdentity center samples)
    (sumIncrementsAreProjectionLeakages center samples)

------------------------------------------------------------------------
-- Helicity gives one rigorous physical reading of a signed orientation lane.
------------------------------------------------------------------------

data HelicitySign : Set where
  positiveHelicity : HelicitySign
  negativeHelicity : HelicitySign

helicityEigenvalue : HelicitySign → ℚ → ℚ
helicityEigenvalue positiveHelicity magnitude = magnitude
helicityEigenvalue negativeHelicity magnitude = - magnitude

oppositeHelicityEigenvaluesCancel :
  (magnitude : ℚ) →
  helicityEigenvalue positiveHelicity magnitude
  + helicityEigenvalue negativeHelicity magnitude
  ≡ 0ℚ
oppositeHelicityEigenvaluesCancel magnitude =
  ℚRing.solve-∀ magnitude

data BalancedOrientation : Set where
  positiveOrientation : BalancedOrientation
  negativeOrientation : BalancedOrientation

orientationOfHelicity : HelicitySign → BalancedOrientation
orientationOfHelicity positiveHelicity = positiveOrientation
orientationOfHelicity negativeHelicity = negativeOrientation

positiveAndNegativeHelicityHaveOppositeOrientations :
  orientationOfHelicity positiveHelicity ≡ positiveOrientation
  × orientationOfHelicity negativeHelicity ≡ negativeOrientation
positiveAndNegativeHelicityHaveOppositeOrientations = refl , refl

record NSClayCrossPollinationBoundary : Set where
  constructor nsClayCrossPollinationBoundary
  field
    finiteCommutatorIsOffDiagonalLeakage : Bool
    finiteCommutatorIsOffDiagonalLeakageIsTrue :
      finiteCommutatorIsOffDiagonalLeakage ≡ true
    projectionIdentitySuppliesContinuumSixThreeBound : Bool
    projectionIdentitySuppliesContinuumSixThreeBoundIsFalse :
      projectionIdentitySuppliesContinuumSixThreeBound ≡ false

canonicalNSClayCrossPollinationBoundary : NSClayCrossPollinationBoundary
canonicalNSClayCrossPollinationBoundary =
  nsClayCrossPollinationBoundary true refl false refl

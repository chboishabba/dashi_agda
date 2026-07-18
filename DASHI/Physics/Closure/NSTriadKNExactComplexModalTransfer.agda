module DASHI.Physics.Closure.NSTriadKNExactComplexModalTransfer where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNExactRingSolverBridge as RingBridge
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Exact complex C^3 carrier over the repository's commutative scalar ring.
--
-- This module supplies a literal complex-vector source for modal transfer data
-- and proves transfer conservation.  It deliberately does not identify the
-- pair flux below with the full Leray-projected Navier--Stokes convolution;
-- that Fourier/PDE identification is a separate theorem boundary.
------------------------------------------------------------------------

record Complex (K : Algebra.ExactOrderedCommutativeRing) : Set where
  constructor complex
  field
    real imaginary : Scalar.Scalar (Algebra.orderedScalar K)

open Complex public

complexZero :
  (K : Algebra.ExactOrderedCommutativeRing) → Complex K
complexZero K = complex (Scalar.zero S) (Scalar.zero S)
  where S = Algebra.orderedScalar K

complexAdd :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Complex K → Complex K → Complex K
complexAdd K x y =
  complex
    (Scalar._+_ S (real x) (real y))
    (Scalar._+_ S (imaginary x) (imaginary y))
  where S = Algebra.orderedScalar K

complexNeg :
  (K : Algebra.ExactOrderedCommutativeRing) → Complex K → Complex K
complexNeg K x =
  complex (Scalar.neg S (real x)) (Scalar.neg S (imaginary x))
  where S = Algebra.orderedScalar K

complexConjugate :
  (K : Algebra.ExactOrderedCommutativeRing) → Complex K → Complex K
complexConjugate K x =
  complex (real x) (Scalar.neg S (imaginary x))
  where S = Algebra.orderedScalar K

complexMul :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Complex K → Complex K → Complex K
complexMul K x y =
  complex
    (Scalar._+_ S
      (Scalar._*_ S (real x) (real y))
      (Scalar.neg S (Scalar._*_ S (imaginary x) (imaginary y))))
    (Scalar._+_ S
      (Scalar._*_ S (real x) (imaginary y))
      (Scalar._*_ S (imaginary x) (real y)))
  where S = Algebra.orderedScalar K

record Complex3 (K : Algebra.ExactOrderedCommutativeRing) : Set where
  constructor complex3
  field
    component1 component2 component3 : Complex K

open Complex3 public

-- Imaginary part of conj(x) * y.  This is an exact real scalar and is the
-- elementary skew-Hermitian pair flux used below.
skewPairScalar :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Complex K → Complex K → Scalar.Scalar (Algebra.orderedScalar K)
skewPairScalar K x y =
  Scalar._+_ S
    (Scalar._*_ S (real x) (imaginary y))
    (Scalar.neg S (Scalar._*_ S (imaginary x) (real y)))
  where S = Algebra.orderedScalar K

complex3PairFlux :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Complex3 K → Complex3 K → Scalar.Scalar (Algebra.orderedScalar K)
complex3PairFlux K x y =
  Scalar._+_ S
    (skewPairScalar K (component1 x) (component1 y))
    (Scalar._+_ S
      (skewPairScalar K (component2 x) (component2 y))
      (skewPairScalar K (component3 x) (component3 y)))
  where S = Algebra.orderedScalar K

------------------------------------------------------------------------
-- Conserved modal allocation.
--
-- Two exact C^3 pair fluxes determine the first two labelled modal transfers;
-- the third is their additive balancing transfer.  Conservation is therefore
-- a theorem of the concrete commutative ring, not a record field supplied by a
-- caller or a sampled numerical receipt.
------------------------------------------------------------------------

exactComplexModalTransfer :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (τ : Lattice.LatticeTriad) →
  Complex3 K → Complex3 K → Complex3 K →
  Energy.ModalTriadTransfer (Algebra.orderedScalar K) τ
exactComplexModalTransfer K τ uLeft uRight uOut = record
  { transferLeft = leftFlux
  ; transferRight = rightFlux
  ; transferOut = Scalar.neg S (Scalar._+_ S leftFlux rightFlux)
  ; conservation = RingBridge.addInverseRight K
      (Scalar._+_ S leftFlux rightFlux)
  }
  where
  S = Algebra.orderedScalar K
  leftFlux = complex3PairFlux K uLeft uRight
  rightFlux = complex3PairFlux K uRight uOut

ComplexVelocityField :
  (K : Algebra.ExactOrderedCommutativeRing) → Set
ComplexVelocityField K = Lattice.LatticeMode3 → Complex3 K

exactComplexZeroSumTransferField :
  (K : Algebra.ExactOrderedCommutativeRing) →
  ComplexVelocityField K →
  Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)
exactComplexZeroSumTransferField K velocity σ =
  exactComplexModalTransfer K τ
    (velocity (Lattice.left τ))
    (velocity (Lattice.right τ))
    (velocity (Lattice.out τ))
  where
  τ = Energy.triad σ

exactComplexModalTransferConservation :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (τ : Lattice.LatticeTriad) →
  (uLeft uRight uOut : Complex3 K) →
  Scalar._+_ (Algebra.orderedScalar K)
    (Scalar._+_ (Algebra.orderedScalar K)
      (Energy.transferLeft
        (exactComplexModalTransfer K τ uLeft uRight uOut))
      (Energy.transferRight
        (exactComplexModalTransfer K τ uLeft uRight uOut)))
    (Energy.transferOut
      (exactComplexModalTransfer K τ uLeft uRight uOut)) ≡
  Scalar.zero (Algebra.orderedScalar K)
exactComplexModalTransferConservation K τ uLeft uRight uOut =
  Energy.conservation (exactComplexModalTransfer K τ uLeft uRight uOut)

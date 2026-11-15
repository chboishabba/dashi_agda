module DASHI.Mathematics.Symmetry.TetragonalIntegerMetricPairingExact where

-- Concrete Z^3 instance of the generator-certified all-D4h pairing theorem.
-- Reuses the integer ring solver already used by DASHI.Physics.
-- Classical signed-orthogonal crystal symmetry (IUCr/Weyl prior art);
-- this new module is an implementation adapter, not a physical finding.
--
-- Axial coefficients can be arbitrary integers. Positive real metric
-- parameters, actual cell constants and Bravais centring require a
-- separately typed physical metric / lattice-basis instance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _*_; -_; +_)
import Data.Integer.Properties as IntP
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as T
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.TetragonalReciprocalPairingExact as Pair

module RingZ = NR IntRS.ring
open RingZ using (Κ; Ι; _⊕_; _⊗_; ⊝_; _⊜_; solve)

integerSignedCarrier : T.SignedCarrier ℤ
integerSignedCarrier = record
  { negate = -_
  ; negateTwice = IntP.neg-involutive
  }

-- Conventional tetragonal coordinate form with independent in-plane
-- and vertical scalar weights (a,a,c).
weightedDot : ℤ → ℤ → T.Triple ℤ → T.Triple ℤ → ℤ
weightedDot a c (T.xyz x y z) (T.xyz u v w) =
  (a * (x * u) + a * (y * v)) + c * (z * w)

weightedR :
  (a c : ℤ) (p k : T.Triple ℤ) →
  weightedDot a c (T.R integerSignedCarrier p)
                  (T.R integerSignedCarrier k) ≡
  weightedDot a c p k
weightedR a c (T.xyz x y z) (T.xyz u v w) =
  RingZ.solve 6
    (λ x y z u v w →
      ( ((Κ a ⊗ (⊝ y ⊗ ⊝ v))
         ⊕ (Κ a ⊗ (x ⊗ u)))
        ⊕ (Κ c ⊗ (z ⊗ w))
      , ((Κ a ⊗ (x ⊗ u))
         ⊕ (Κ a ⊗ (y ⊗ v)))
        ⊕ (Κ c ⊗ (z ⊗ w)) ))
    refl x y z u v w

weightedV :
  (a c : ℤ) (p k : T.Triple ℤ) →
  weightedDot a c (T.V integerSignedCarrier p)
                  (T.V integerSignedCarrier k) ≡
  weightedDot a c p k
weightedV a c (T.xyz x y z) (T.xyz u v w) =
  RingZ.solve 6
    (λ x y z u v w →
      ( ((Κ a ⊗ (x ⊗ u))
         ⊕ (Κ a ⊗ (⊝ y ⊗ ⊝ v)))
        ⊕ (Κ c ⊗ (z ⊗ w))
      , ((Κ a ⊗ (x ⊗ u))
         ⊕ (Κ a ⊗ (y ⊗ v)))
        ⊕ (Κ c ⊗ (z ⊗ w)) ))
    refl x y z u v w

weightedH :
  (a c : ℤ) (p k : T.Triple ℤ) →
  weightedDot a c (T.H integerSignedCarrier p)
                  (T.H integerSignedCarrier k) ≡
  weightedDot a c p k
weightedH a c (T.xyz x y z) (T.xyz u v w) =
  RingZ.solve 6
    (λ x y z u v w →
      ( ((Κ a ⊗ (x ⊗ u))
         ⊕ (Κ a ⊗ (y ⊗ v)))
        ⊕ (Κ c ⊗ (⊝ z ⊗ ⊝ w))
      , ((Κ a ⊗ (x ⊗ u))
         ⊕ (Κ a ⊗ (y ⊗ v)))
        ⊕ (Κ c ⊗ (z ⊗ w)) ))
    refl x y z u v w

concretePairing : (a c : ℤ) → Pair.PairingLaws ℤ
concretePairing a c = record
  { signed = integerSignedCarrier
  ; dot = weightedDot a c
  ; rotateInvariant = weightedR a c
  ; verticalInvariant = weightedV a c
  ; horizontalInvariant = weightedH a c
  }

-- Universal over all 16 D4h elements, all Z^3 x Z^3, and all Z weights.
fullTetragonalMetricInvariant :
  (a c : ℤ) (g : D.D4h) (p k : T.Triple ℤ) →
  weightedDot a c (T.act integerSignedCarrier g p)
                  (T.act integerSignedCarrier g k)
  ≡ weightedDot a c p k
fullTetragonalMetricInvariant a c g p k =
  Pair.fullPairingInvariant (concretePairing a c) g p k

-- For the standard direct/reciprocal integer index pairing, use
-- a=c=1. Explicit canonical integer one avoids a new abstraction.
standardFourierPairingInvariant :
  (g : D.D4h) (p k : T.Triple ℤ) →
  weightedDot (+ 1) (+ 1)
    (T.act integerSignedCarrier g p)
    (T.act integerSignedCarrier g k)
  ≡ weightedDot (+ 1) (+ 1) p k
standardFourierPairingInvariant =
  fullTetragonalMetricInvariant (+ 1) (+ 1)

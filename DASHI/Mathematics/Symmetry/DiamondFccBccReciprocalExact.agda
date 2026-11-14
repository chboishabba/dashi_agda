module DASHI.Mathematics.Symmetry.DiamondFccBccReciprocalExact where

-- Exact fcc direct-lattice ↔ bcc reciprocal-index inclusion.
-- Physical convention: fcc coordinates are conventional cubic a/4,
-- reciprocal indices are multiples of 2π/a. Bloch phase integral
-- precisely when dot(quarter-index, reciprocal-index) divisible by 4.
-- Classical prior art: reciprocal(fcc)=bcc; this module proves the
-- constructive "bcc indices pair integrally" direction. The full
-- converse lattice characterisation remains separately open.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Integer using (ℤ; +_; _+_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Mathematics.Symmetry.DiamondFccPrimitiveGlideExact as FCC
import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as T
import DASHI.Mathematics.Symmetry.TetragonalIntegerMetricPairingExact as Metric

module RingZ = NR IntRS.ring
open RingZ using (Κ; Ι; _⊕_; _⊗_; solve)

parityBit : Bool → ℤ
parityBit false = + 0
parityBit true = + 1

-- This parametrization is canonical for parity=0 or parity=1:
-- k=(2a+s,2b+s,2c+s) has all three components of equal parity.
record BccReciprocalIndex : Set where
  constructor bcc
  field
    a b c : ℤ
    odd : Bool
open BccReciprocalIndex public

sharedParityVector : ℤ → ℤ → ℤ → ℤ → T.Triple ℤ
sharedParityVector a b c s =
  T.xyz (((+ 2) * a) + s)
        (((+ 2) * b) + s)
        (((+ 2) * c) + s)

toReciprocalVector : BccReciprocalIndex → T.Triple ℤ
toReciprocalVector (bcc a b c odd) =
  sharedParityVector a b c (parityBit odd)

windingValue : FCC.PrimitiveFcc → ℤ → ℤ → ℤ → ℤ → ℤ
windingValue (FCC.primitive u v w) a b c s =
  ((a * (v + w) + b * (u + w)) + c * (u + v))
  + s * ((u + v) + w)

dotQuarterIndex : T.Triple ℤ → T.Triple ℤ → ℤ
dotQuarterIndex = Metric.weightedDot (+ 1) (+ 1)

-- Works for ANY common parity-offset integer s; canonical bcc
-- chooses s∈{0,1}. The lattice arithmetic does not require division.
fccSharedParityWinding :
  (u v w a b c s : ℤ) →
  dotQuarterIndex
    (FCC.fccPoint (FCC.primitive u v w))
    (sharedParityVector a b c s)
    ≡ (+ 4) * (windingValue (FCC.primitive u v w) a b c s)
fccSharedParityWinding u v w a b c s =
  RingZ.solve 7
    (λ u v w a b c s →
      let x = Κ (+ 2) ⊗ (v ⊕ w)
          y = Κ (+ 2) ⊗ (u ⊕ w)
          z = Κ (+ 2) ⊗ (u ⊕ v)
          kx = (Κ (+ 2) ⊗ a) ⊕ s
          ky = (Κ (+ 2) ⊗ b) ⊕ s
          kz = (Κ (+ 2) ⊗ c) ⊕ s
          n = (((a ⊗ (v ⊕ w)) ⊕ (b ⊗ (u ⊕ w)))
               ⊕ (c ⊗ (u ⊕ v)))
               ⊕ (s ⊗ ((u ⊕ v) ⊕ w))
      in ( (((Κ (+ 1) ⊗ (x ⊗ kx))
              ⊕ (Κ (+ 1) ⊗ (y ⊗ ky)))
             ⊕ (Κ (+ 1) ⊗ (z ⊗ kz)))
         , (Κ (+ 4) ⊗ n) ))
    refl u v w a b c s

-- The integrated reciprocal phase is 2π * windingValue(...),
-- so translating by any primitive fcc lattice vector contributes
-- unit Bloch phase for the sampled bcc reciprocal indices.
fccBccIntegrality :
  (p : FCC.PrimitiveFcc) (k : BccReciprocalIndex) →
  dotQuarterIndex (FCC.fccPoint p) (toReciprocalVector k)
  ≡ (+ 4) * windingValue p (a k) (b k) (c k) (parityBit (odd k))
fccBccIntegrality (FCC.primitive u v w) (bcc a b c odd) =
  fccSharedParityWinding u v w a b c (parityBit odd)

-- Here the pairing is integer-index arithmetic. The 2π/a unit
-- convention and actual complex exponential character, as well
-- as the converse "every reciprocal vector has equal parity",
-- are distinct downstream proofs.

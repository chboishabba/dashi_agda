module DASHI.Physics.Foundations.Hopf369MarkedTidalCubeExact where

-- Exact rational marked BR144/145 observation, no physical-time commutation.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Core.GovernedIndexedResidualCubeExact as C
import DASHI.Core.GovernedDiagramCore as G

-- The actual BR145 odd mixed component is 16 epsilon / p².
-- Work on the normalized readout p² T34 / 16, whose value is epsilon.
-- Retain the even diagonal scale independently, including zero amplitude.
record Marked : Set where
  constructor marked
  field
    evenScale signedAmplitude : ℚ
open Marked public

record Split : Set where
  constructor split
  field
    coarse residual : ℚ
open Split public

observe : Marked → Split
observe (marked q e) = split q e

reopen : Split → Marked
reopen (split q e) = marked q e

reopenObserve : (a : Marked) → reopen (observe a) ≡ a
reopenObserve (marked q e) = refl

observeReopen : (a : Split) → observe (reopen a) ≡ a
observeReopen (split q e) = refl

-- Reflection changes only the marked mixed observation.
-- This parameterized map permits independent history labels outside the cube.
reflect : ℚ → Marked → Marked
reflect k (marked q e) = marked q (k - e)

reflectSplit : ℚ → Split → Split
reflectSplit k (split q e) = split q (k - e)

observeReflect : (k : ℚ) (a : Marked) →
  observe (reflect k a) ≡ reflectSplit k (observe a)
observeReflect k (marked q e) = refl

-- The x axis is observation, y is marked reflection, z is exact
-- representation reopening (identity on the appropriate chart).
-- These are chart operations, not time or refinement evolution.
cube : ℚ → C.Cube
cube k = record
  { A = Marked ; B = Split ; C = Marked ; D = Split
  ; E = Marked ; F = Split ; H = Marked ; I = Split
  ; x00 = observe ; x10 = observe ; x01 = observe ; x11 = observe
  ; y00 = reflect k ; y10 = reflectSplit k
  ; y01 = reflect k ; y11 = reflectSplit k
  ; z00 = λ a → reopen (observe a)
  ; z10 = λ a → observe (reopen a)
  ; z01 = λ a → reopen (observe a)
  ; z11 = λ a → observe (reopen a)
  }

faces : (k : ℚ) → C.Faces (cube k)
faces k = record
  { Rxy0 = λ a → Split ; Rxz0 = λ a → Split ; Ryz0 = λ a → Split
  ; Rxy1 = λ a → Split ; Rxz1 = λ a → Split ; Ryz1 = λ a → Split
  }

exact : (k : ℚ) → C.ExactFaces (cube k) (faces k)
exact k = record
  { pxy0 = G.commutingSquareWitness (λ { (marked q e) → refl })
  ; pxz0 = G.commutingSquareWitness (λ { (marked q e) → refl })
  ; pyz0 = G.commutingSquareWitness (λ { (marked q e) → refl })
  ; pxy1 = G.commutingSquareWitness (λ { (marked q e) → refl })
  ; pxz1 = G.commutingSquareWitness (λ { (marked q e) → refl })
  ; pyz1 = G.commutingSquareWitness (λ { (split q e) → refl })
  }

endpoint : (k : ℚ) (a : Marked) →
  C.xyz (cube k) a ≡ C.zyx (cube k) a
endpoint k = C.xyz-zyx (exact k)

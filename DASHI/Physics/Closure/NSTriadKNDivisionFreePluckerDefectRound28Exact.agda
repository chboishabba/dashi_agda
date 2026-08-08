module DASHI.Physics.Closure.NSTriadKNDivisionFreePluckerDefectRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hermann Grassmann.
-- Title: "Die lineale Ausdehnungslehre" (1844).
-- DOI: not applicable; historical source.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Replace angular division by a homogeneous cross-multiplied defect.  Integer
-- mode scaling is defined explicitly and the Plucker numerator is proved
-- biquadratically homogeneous:
--
--   |(a p) cross (b q)|^2 = (a b)^2 |p cross q|^2.
--
-- The norm square obeys |a p|^2 = a^2 |p|^2, and every pair of parallel
-- scaled modes has exactly zero Plucker numerator.  No nonzero denominator,
-- normalized direction or inverse frequency is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_; -_; _≤_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plucker

module RingZ = NR IntRS.ring
open RingZ using (_⊕_; _⊗_; ⊝_; solve)

scaleMode : ℤ → Z3.FourierMode → Z3.FourierMode
scaleMode scalar mode =
  Z3.mode
    (scalar * Z3.kx mode)
    (scalar * Z3.ky mode)
    (scalar * Z3.kz mode)

pluckerScaleX : ∀ leftScale rightScale p q →
  Plucker.pluckerX
    (scaleMode leftScale p) (scaleMode rightScale q)
  ≡
  (leftScale * rightScale) * Plucker.pluckerX p q
pluckerScaleX leftScale rightScale
  (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 8
    (λ a b px py pz qx qy qz →
      (((a ⊗ py) ⊗ (b ⊗ qz))
        ⊕ ⊝ ((a ⊗ pz) ⊗ (b ⊗ qy))
      , (a ⊗ b) ⊗ ((py ⊗ qz) ⊕ ⊝ (pz ⊗ qy))))
    refl leftScale rightScale px py pz qx qy qz

pluckerScaleY : ∀ leftScale rightScale p q →
  Plucker.pluckerY
    (scaleMode leftScale p) (scaleMode rightScale q)
  ≡
  (leftScale * rightScale) * Plucker.pluckerY p q
pluckerScaleY leftScale rightScale
  (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 8
    (λ a b px py pz qx qy qz →
      (((a ⊗ pz) ⊗ (b ⊗ qx))
        ⊕ ⊝ ((a ⊗ px) ⊗ (b ⊗ qz))
      , (a ⊗ b) ⊗ ((pz ⊗ qx) ⊕ ⊝ (px ⊗ qz))))
    refl leftScale rightScale px py pz qx qy qz

pluckerScaleZ : ∀ leftScale rightScale p q →
  Plucker.pluckerZ
    (scaleMode leftScale p) (scaleMode rightScale q)
  ≡
  (leftScale * rightScale) * Plucker.pluckerZ p q
pluckerScaleZ leftScale rightScale
  (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 8
    (λ a b px py pz qx qy qz →
      (((a ⊗ px) ⊗ (b ⊗ qy))
        ⊕ ⊝ ((a ⊗ py) ⊗ (b ⊗ qx))
      , (a ⊗ b) ⊗ ((px ⊗ qy) ⊕ ⊝ (py ⊗ qx))))
    refl leftScale rightScale px py pz qx qy qz

pluckerNormScale : ∀ leftScale rightScale p q →
  Plucker.pluckerNormSquared
    (scaleMode leftScale p) (scaleMode rightScale q)
  ≡
  ((leftScale * rightScale) * (leftScale * rightScale))
  * Plucker.pluckerNormSquared p q
pluckerNormScale leftScale rightScale p q
  rewrite pluckerScaleX leftScale rightScale p q
        | pluckerScaleY leftScale rightScale p q
        | pluckerScaleZ leftScale rightScale p q =
  RingZ.solve 4
    (λ factor x y z →
      ((((factor ⊗ x) ⊗ (factor ⊗ x))
        ⊕ ((factor ⊗ y) ⊗ (factor ⊗ y)))
        ⊕ ((factor ⊗ z) ⊗ (factor ⊗ z))
      , (factor ⊗ factor)
        ⊗ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ (z ⊗ z))))
    refl
    (leftScale * rightScale)
    (Plucker.pluckerX p q)
    (Plucker.pluckerY p q)
    (Plucker.pluckerZ p q)

modeNormScale : ∀ scalar mode →
  Plucker.modeNormSquared (scaleMode scalar mode)
  ≡ (scalar * scalar) * Plucker.modeNormSquared mode
modeNormScale scalar (Z3.mode x y z) =
  RingZ.solve 4
    (λ scalar x y z →
      ((((scalar ⊗ x) ⊗ (scalar ⊗ x))
        ⊕ ((scalar ⊗ y) ⊗ (scalar ⊗ y)))
        ⊕ ((scalar ⊗ z) ⊗ (scalar ⊗ z))
      , (scalar ⊗ scalar)
        ⊗ (((x ⊗ x) ⊕ (y ⊗ y)) ⊕ (z ⊗ z))))
    refl scalar x y z

pluckerSelfNormZero : ∀ mode →
  Plucker.pluckerNormSquared mode mode ≡ + 0
pluckerSelfNormZero (Z3.mode x y z) =
  RingZ.solve 3
    (λ x y z →
      (((((y ⊗ z) ⊕ ⊝ (z ⊗ y))
          ⊗ ((y ⊗ z) ⊕ ⊝ (z ⊗ y)))
        ⊕ (((z ⊗ x) ⊕ ⊝ (x ⊗ z))
          ⊗ ((z ⊗ x) ⊕ ⊝ (x ⊗ z))))
        ⊕ (((x ⊗ y) ⊕ ⊝ (y ⊗ x))
          ⊗ ((x ⊗ y) ⊕ ⊝ (y ⊗ x)))
      , RingZ.Κ (+ 0)))
    refl x y z

parallelScaledModesHaveZeroDefect : ∀ leftScale rightScale direction →
  Plucker.pluckerNormSquared
    (scaleMode leftScale direction)
    (scaleMode rightScale direction)
  ≡ + 0
parallelScaledModesHaveZeroDefect leftScale rightScale direction =
  let
    factor = leftScale * rightScale

    scaled :
      Plucker.pluckerNormSquared
        (scaleMode leftScale direction)
        (scaleMode rightScale direction)
      ≡
      (factor * factor)
      * Plucker.pluckerNormSquared direction direction
    scaled = pluckerNormScale leftScale rightScale direction direction

    zeroProduct :
      (factor * factor)
      * Plucker.pluckerNormSquared direction direction
      ≡ + 0
    zeroProduct
      rewrite pluckerSelfNormZero direction =
      RingZ.solve 1
        (λ coefficient →
          (coefficient ⊗ RingZ.Κ (+ 0), RingZ.Κ (+ 0)))
        refl
        (factor * factor)
  in
  trans scaled zeroProduct

record CrossMultipliedAngularDefect
    (thresholdSquared : ℤ)
    (left right : Z3.FourierMode) : Set where
  constructor cross-multiplied-angular-defect
  field
    defectBound :
      Plucker.pluckerNormSquared left right
      ≤
      thresholdSquared
      * (Plucker.modeNormSquared left
        * Plucker.modeNormSquared right)

open CrossMultipliedAngularDefect public

divisionFreePluckerHomogeneityClosed : Bool
divisionFreePluckerHomogeneityClosed = true

parallelZeroBranchClosed : Bool
parallelZeroBranchClosed = true

continuumDirectionalNearFieldTaxClosed : Bool
continuumDirectionalNearFieldTaxClosed = false

parallelZeroBranchClosedIsTrue : parallelZeroBranchClosed ≡ true
parallelZeroBranchClosedIsTrue = refl

continuumDirectionalNearFieldTaxClosedIsFalse :
  continuumDirectionalNearFieldTaxClosed ≡ false
continuumDirectionalNearFieldTaxClosedIsFalse = refl

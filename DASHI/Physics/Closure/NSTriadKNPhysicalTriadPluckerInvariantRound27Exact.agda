module DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hermann Grassmann,
-- "Die lineale Ausdehnungslehre" (1844); historical source, no DOI.
--
-- Authors: Constantin and Fefferman.
-- Title: "Direction of vorticity and the problem of global regularity for the
-- Navier-Stokes equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Attach division-free plane geometry to every physical resonant triad.  The
-- three Plucker coordinates are the components of p cross q.  We prove the
-- full Gram determinant identity
--
--   |p cross q|^2 = |p|^2 |q|^2 - (p dot q)^2
--
-- over the exact integer lattice and prove that swapping the two inputs
-- negates every oriented coordinate while preserving the squared area.
-- This distinguishes shell magnitude from interaction-plane geometry without
-- normalising either frequency vector.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _-_; _*_; -_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Data.Product.Base using (_×_; _,_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

module RingZ = NR IntRS.ring
open RingZ using (Κ; Ι; _⊕_; _⊗_; ⊝_; _⊜_; solve)

pluckerX pluckerY pluckerZ :
  Z3.FourierMode → Z3.FourierMode → ℤ
pluckerX p q = Z3.ky p * Z3.kz q - Z3.kz p * Z3.ky q
pluckerY p q = Z3.kz p * Z3.kx q - Z3.kx p * Z3.kz q
pluckerZ p q = Z3.kx p * Z3.ky q - Z3.ky p * Z3.kx q

dotMode : Z3.FourierMode → Z3.FourierMode → ℤ
dotMode p q =
  Z3.kx p * Z3.kx q
  + Z3.ky p * Z3.ky q
  + Z3.kz p * Z3.kz q

modeNormSquared : Z3.FourierMode → ℤ
modeNormSquared p = dotMode p p

pluckerNormSquared : Z3.FourierMode → Z3.FourierMode → ℤ
pluckerNormSquared p q =
  pluckerX p q * pluckerX p q
  + pluckerY p q * pluckerY p q
  + pluckerZ p q * pluckerZ p q

pluckerGramIdentity : ∀ p q →
  pluckerNormSquared p q
  ≡ modeNormSquared p * modeNormSquared q
    - dotMode p q * dotMode p q
pluckerGramIdentity
  (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      ( (((py ⊗ qz ⊕ ⊝ (pz ⊗ qy))
          ⊗ (py ⊗ qz ⊕ ⊝ (pz ⊗ qy)))
        ⊕ ((pz ⊗ qx ⊕ ⊝ (px ⊗ qz))
          ⊗ (pz ⊗ qx ⊕ ⊝ (px ⊗ qz))))
        ⊕ ((px ⊗ qy ⊕ ⊝ (py ⊗ qx))
          ⊗ (px ⊗ qy ⊕ ⊝ (py ⊗ qx))))
      , (((px ⊗ px ⊕ py ⊗ py) ⊕ pz ⊗ pz)
          ⊗ ((qx ⊗ qx ⊕ qy ⊗ qy) ⊕ qz ⊗ qz))
        ⊕ ⊝
          (((px ⊗ qx ⊕ py ⊗ qy) ⊕ pz ⊗ qz)
            ⊗ ((px ⊗ qx ⊕ py ⊗ qy) ⊕ pz ⊗ qz))) ))
    refl px py pz qx qy qz

pluckerSwapX : ∀ p q → pluckerX q p ≡ - pluckerX p q
pluckerSwapX (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      (qy ⊗ pz ⊕ ⊝ (qz ⊗ py)
      , ⊝ (py ⊗ qz ⊕ ⊝ (pz ⊗ qy))))
    refl px py pz qx qy qz

pluckerSwapY : ∀ p q → pluckerY q p ≡ - pluckerY p q
pluckerSwapY (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      (qz ⊗ px ⊕ ⊝ (qx ⊗ pz)
      , ⊝ (pz ⊗ qx ⊕ ⊝ (px ⊗ qz))))
    refl px py pz qx qy qz

pluckerSwapZ : ∀ p q → pluckerZ q p ≡ - pluckerZ p q
pluckerSwapZ (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      (qx ⊗ py ⊕ ⊝ (qy ⊗ px)
      , ⊝ (px ⊗ qy ⊕ ⊝ (py ⊗ qx))))
    refl px py pz qx qy qz

pluckerSwapPreservesSquaredArea : ∀ p q →
  pluckerNormSquared q p ≡ pluckerNormSquared p q
pluckerSwapPreservesSquaredArea p q
  rewrite pluckerSwapX p q
        | pluckerSwapY p q
        | pluckerSwapZ p q =
  RingZ.solve 3
    (λ x y z →
      (((⊝ x ⊗ ⊝ x) ⊕ (⊝ y ⊗ ⊝ y)) ⊕ (⊝ z ⊗ ⊝ z)
      , ((x ⊗ x ⊕ y ⊗ y) ⊕ z ⊗ z)))
    refl (pluckerX p q) (pluckerY p q) (pluckerZ p q)

record PhysicalTriadPlaneInvariant
    (triad : Physical.PhysicalTriadIncidence) : Set where
  constructor physical-triad-plane-invariant
  field
    xCoordinate : ℤ
    yCoordinate : ℤ
    zCoordinate : ℤ
    squaredArea : ℤ
    xMeaning : xCoordinate ≡ pluckerX (Physical.p triad) (Physical.q triad)
    yMeaning : yCoordinate ≡ pluckerY (Physical.p triad) (Physical.q triad)
    zMeaning : zCoordinate ≡ pluckerZ (Physical.p triad) (Physical.q triad)
    areaMeaning : squaredArea ≡
      modeNormSquared (Physical.p triad)
      * modeNormSquared (Physical.q triad)
      - dotMode (Physical.p triad) (Physical.q triad)
        * dotMode (Physical.p triad) (Physical.q triad)

open PhysicalTriadPlaneInvariant public

canonicalPhysicalTriadPlaneInvariant :
  (triad : Physical.PhysicalTriadIncidence) →
  PhysicalTriadPlaneInvariant triad
canonicalPhysicalTriadPlaneInvariant triad =
  physical-triad-plane-invariant
    (pluckerX (Physical.p triad) (Physical.q triad))
    (pluckerY (Physical.p triad) (Physical.q triad))
    (pluckerZ (Physical.p triad) (Physical.q triad))
    (pluckerNormSquared (Physical.p triad) (Physical.q triad))
    refl refl refl
    (pluckerGramIdentity (Physical.p triad) (Physical.q triad))

physicalTriadPluckerGeometryClosed : Bool
physicalTriadPluckerGeometryClosed = true

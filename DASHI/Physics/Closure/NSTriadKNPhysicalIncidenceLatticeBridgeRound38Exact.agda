module DASHI.Physics.Closure.NSTriadKNPhysicalIncidenceLatticeBridgeRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- DASHI CONTRIBUTION
--
-- Close the carrier/conjugate-output part of the remaining F4 same-object
-- seam.  The repository has two exact integer-mode records:
--
--   * `FourierMode`, used by the physical convolution/Complex3 coefficient;
--   * `LatticeMode3`, used by the direct finite convolution enumeration.
--
-- They are literally the same Z^3 coordinates.  This module defines the two
-- conversions, proves both round trips and compatibility with addition and
-- negation, and maps every physical incidence
--
--   p + q = k
--
-- to the direct-convolution zero-sum convention
--
--   (p , q , -k),
--   p + q - k = 0.
--
-- In particular the Boolean `zeroSum?` used by the finite convolution list is
-- proved true from the physical incidence resonance, rather than assumed.
-- This leaves F4 with list/shell partition and coefficient-normalization
-- identification, not a hidden mismatch between the two mode carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Properties as ℤP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Z3Add
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

fourierToLattice : Z3.FourierMode → Lattice.LatticeMode3
fourierToLattice mode =
  Lattice.mkLatticeMode3 (Z3.kx mode) (Z3.ky mode) (Z3.kz mode)

latticeToFourier : Lattice.LatticeMode3 → Z3.FourierMode
latticeToFourier mode =
  Z3.mode (Lattice.k₁ mode) (Lattice.k₂ mode) (Lattice.k₃ mode)

fourierLatticeRoundtrip :
  ∀ mode → latticeToFourier (fourierToLattice mode) ≡ mode
fourierLatticeRoundtrip (Z3.mode x y z) = refl

latticeFourierRoundtrip :
  ∀ mode → fourierToLattice (latticeToFourier mode) ≡ mode
latticeFourierRoundtrip (Lattice.mkLatticeMode3 x y z) = refl

latticeModeExt :
  ∀ {left right : Lattice.LatticeMode3} →
  Lattice.k₁ left ≡ Lattice.k₁ right →
  Lattice.k₂ left ≡ Lattice.k₂ right →
  Lattice.k₃ left ≡ Lattice.k₃ right →
  left ≡ right
latticeModeExt
  {Lattice.mkLatticeMode3 lx ly lz}
  {Lattice.mkLatticeMode3 .lx .ly .lz}
  refl refl refl = refl

latticeAdd :
  Lattice.LatticeMode3 → Lattice.LatticeMode3 → Lattice.LatticeMode3
latticeAdd left right =
  Lattice.mkLatticeMode3
    (Lattice.k₁ left Data.Integer.Base.+ Lattice.k₁ right)
    (Lattice.k₂ left Data.Integer.Base.+ Lattice.k₂ right)
    (Lattice.k₃ left Data.Integer.Base.+ Lattice.k₃ right)

fourierToLatticeNegation : ∀ mode →
  fourierToLattice (Z3.negateMode mode)
  ≡ Lattice.modeNeg (fourierToLattice mode)
fourierToLatticeNegation (Z3.mode x y z) = refl

fourierToLatticeAddition : ∀ left right →
  fourierToLattice (Z3.addMode left right)
  ≡ latticeAdd (fourierToLattice left) (fourierToLattice right)
fourierToLatticeAddition
  (Z3.mode lx ly lz) (Z3.mode rx ry rz) = refl

physicalIncidenceAsZeroSumTriad :
  Physical.PhysicalTriadIncidence → Lattice.LatticeTriad
physicalIncidenceAsZeroSumTriad tau =
  Lattice.mkLatticeTriad
    (fourierToLattice (Physical.p tau))
    (fourierToLattice (Physical.q tau))
    (Lattice.modeNeg (fourierToLattice (Physical.k tau)))

physicalIncidenceLeftMeaning : ∀ tau →
  Lattice.left (physicalIncidenceAsZeroSumTriad tau)
  ≡ fourierToLattice (Physical.p tau)
physicalIncidenceLeftMeaning tau = refl

physicalIncidenceRightMeaning : ∀ tau →
  Lattice.right (physicalIncidenceAsZeroSumTriad tau)
  ≡ fourierToLattice (Physical.q tau)
physicalIncidenceRightMeaning tau = refl

physicalIncidenceConjugateOutputMeaning : ∀ tau →
  Lattice.out (physicalIncidenceAsZeroSumTriad tau)
  ≡ Lattice.modeNeg (fourierToLattice (Physical.k tau))
physicalIncidenceConjugateOutputMeaning tau = refl

physicalIncidenceTriadSumZero : ∀ tau →
  Lattice.triadSum (physicalIncidenceAsZeroSumTriad tau)
  ≡ Lattice.mkLatticeMode3 (Data.Integer.Base.+ 0)
      (Data.Integer.Base.+ 0) (Data.Integer.Base.+ 0)
physicalIncidenceTriadSumZero
    (Physical.physicalTriad
      (Z3.mode px py pz)
      (Z3.mode qx qy qz)
      (Z3.mode kx ky kz)
      resonance)
  with cong Z3.kx resonance | cong Z3.ky resonance | cong Z3.kz resonance
... | xRes | yRes | zRes =
  latticeModeExt
    (trans
      (cong (λ value → value Data.Integer.Base.+ (Data.Integer.Base.- kx)) xRes)
      (ℤP.+-inverseʳ kx))
    (trans
      (cong (λ value → value Data.Integer.Base.+ (Data.Integer.Base.- ky)) yRes)
      (ℤP.+-inverseʳ ky))
    (trans
      (cong (λ value → value Data.Integer.Base.+ (Data.Integer.Base.- kz)) zRes)
      (ℤP.+-inverseʳ kz))

physicalIncidenceZeroSumBoolean : ∀ tau →
  Lattice.zeroSum? (physicalIncidenceAsZeroSumTriad tau) ≡ true
physicalIncidenceZeroSumBoolean tau =
  trans
    (cong Lattice.zeroMode? (physicalIncidenceTriadSumZero tau))
    refl

physicalIncidenceResonanceFromZeroSumConvention : ∀ tau →
  Z3.addMode (Physical.p tau) (Physical.q tau)
  ≡ Physical.k tau
physicalIncidenceResonanceFromZeroSumConvention = Physical.resonance

physicalIncidenceLatticeCarrierBridgeClosed : Bool
physicalIncidenceLatticeCarrierBridgeClosed = true

physicalIncidenceLatticeCarrierBridgeClosedIsTrue :
  physicalIncidenceLatticeCarrierBridgeClosed ≡ true
physicalIncidenceLatticeCarrierBridgeClosedIsTrue = refl

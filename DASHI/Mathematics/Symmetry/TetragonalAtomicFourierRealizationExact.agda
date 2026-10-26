module DASHI.Mathematics.Symmetry.TetragonalAtomicFourierRealizationExact where

-- Real integer-lattice consumer of the crystal model, with distinct
-- direct-space and reciprocal-space types. Uses the canonical atomic
-- index from the DASHI 369 chemistry owner and existing NS Fourier
-- modes. No physical compound, calibrated band energy, or measurement
-- is inferred from a Bravais type alone.
--
-- Classical crystallography: IUCr International Tables Vol. A,
-- P4/mmm, No. 123 (point group 4/mmm, primitive tetragonal).
-- This is a source-level formal adapter, pending Agda compiler receipt.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Symmetry.CrystalRealizationConsumerContractExact as C
import DASHI.Mathematics.Symmetry.CrystalClassificationSevenFourteenExact as L
import DASHI.Mathematics.Symmetry.CrystalPointGroup32CatalogExact as Point
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.TetragonalFourierLatticeBridgeExact as F
import DASHI.Mathematics.Symmetry.TetragonalPrimitiveSeitzExact as Seitz
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic
import DASHI.Physics.Closure.NSIntegerFourierLattice as Fourier

-- This wrapper prevents confusing a Bravais lattice position with a
-- wavevector, even though both use integer triples in standard axes.
record DirectPoint : Set where
  constructor directPoint
  field
    coordinate : Fourier.FourierMode
open DirectPoint public

actDirect : D.D4h → DirectPoint → DirectPoint
actDirect g (directPoint p) = directPoint (F.actMode g p)

directIdentity : (p : DirectPoint) →
  actDirect D.identity p ≡ p
directIdentity (directPoint p)
  rewrite Seitz.actModeIdentity p = refl

directCompose : (g h : D.D4h) (p : DirectPoint) →
  actDirect (D.compose g h) p ≡ actDirect g (actDirect h p)
directCompose g h (directPoint p)
  rewrite Seitz.actModeCompose g h p = refl

-- Primitive direct lattice and its integer reciprocal index lattice.
-- For signed Euclidean coordinate matrices, U^{-T}=U. The integer
-- dot product is the discrete index pairing, not a physical unit
-- conversion. Real lattice constants and 2π are separate.
fourierOrthogonal : DirectPoint → Fourier.FourierMode → Set
fourierOrthogonal p k =
  F.modeWeightedPairing (+ 1) (+ 1) (coordinate p) k ≡ + 0

-- The energy fixture is quadratic in k, hence not the earlier
-- constant-valued synthetic placeholder. It is a shell observable,
-- NOT a band eigenvalue of an interacting Hamiltonian.
momentumShell : Fourier.FourierMode → ℤ
momentumShell k = F.modeWeightedPairing (+ 1) (+ 1) k k

tetragonalAtomicRealization :
  (species : Atomic.AtomicIndex) →
  C.CrystalRealization
    D.D4h DirectPoint Fourier.FourierMode DirectPoint ℤ
tetragonalAtomicRealization species = record
  { bravais = L.tP
  ; pointGroup = Point.pg4OverMMM
  ; classificationCompatible = refl
  ; identity = D.identity
  ; compose = D.compose
  ; directAction = actDirect
  ; reciprocalAction = F.actMode
  ; directIdentity = directIdentity
  ; reciprocalIdentity = Seitz.actModeIdentity
  ; directCompose = directCompose
  ; reciprocalCompose = Seitz.actModeCompose
  ; Pairing = fourierOrthogonal
  ; pairingCovariant = λ g p k orth →
      trans
        (F.modePairingInvariant (+ 1) (+ 1)
          g (coordinate p) k)
        orth
  ; sitePosition = λ p → p
  ; siteAtom = λ p → species
  ; siteAction = actDirect
  ; sitePositionEquivariant = λ g p → refl
  ; siteSpeciesPreserved = λ g p → refl
  ; BandEnergy = momentumShell
  ; bandEnergyInvariant = F.modeShellInvariant (+ 1) (+ 1)
  }

-- Minimal scalar atomic-index instance. Its proton/neutron/electron
-- counts are index data, not a proof of a stable crystallised material.
hydrogenIndex : Atomic.AtomicIndex
hydrogenIndex = Atomic.atomicIndex 1 0 1

tetragonalHydrogenTestFixture :
  C.CrystalRealization
    D.D4h DirectPoint Fourier.FourierMode DirectPoint ℤ
tetragonalHydrogenTestFixture = tetragonalAtomicRealization hydrogenIndex

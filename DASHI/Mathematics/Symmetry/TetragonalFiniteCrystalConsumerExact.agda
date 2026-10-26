module DASHI.Mathematics.Symmetry.TetragonalFiniteCrystalConsumerExact where

-- First concrete instantiation of the shared crystal-consumer contract.
-- It uses the existing 16-element D4h normal form and *eight-site*
-- representation, not an assertion of an infinite Bravais lattice,
-- Bloch spectrum, or actual specimen structure.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Mathematics.Symmetry.CrystalRealizationConsumerContractExact as Contract
import DASHI.Mathematics.Symmetry.CrystalClassificationSevenFourteenExact as Lattice
import DASHI.Mathematics.Symmetry.CrystalPointGroup32CatalogExact as Point
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as NF
import DASHI.Mathematics.Symmetry.TetragonalD4hFullActionExact as Full
import DASHI.Mathematics.Symmetry.TetragonalD4hGeneratorActionExact as Geo
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic

-- A mono-species decorated *finite* site orbit. It is an exact
-- classification/action test fixture, not a real atomic arrangement.
hydrogen : Atomic.AtomicIndex
hydrogen = Atomic.atomicIndex 1 0 1

finiteTetragonalRealization :
  Contract.CrystalRealization
    NF.D4h Geo.Site Geo.Site Geo.Site Nat
finiteTetragonalRealization = record
  { bravais = Lattice.tP
  ; pointGroup = Point.pg4OverMMM
  ; classificationCompatible = refl
  ; identity = NF.identity
  ; compose = NF.compose
  ; directAction = NF.act
  ; reciprocalAction = NF.act
  ; directIdentity = Full.identityActs
  ; reciprocalIdentity = Full.identityActs
  ; directCompose = Full.composeActs
  ; reciprocalCompose = Full.composeActs
  ; Pairing = _≡_
  ; pairingCovariant = λ g x k same → cong (NF.act g) same
  ; sitePosition = λ p → p
  ; siteAtom = λ p → hydrogen
  ; siteAction = NF.act
  ; sitePositionEquivariant = λ g p → refl
  ; siteSpeciesPreserved = λ g p → refl
  ; BandEnergy = λ p → zero
  ; bandEnergyInvariant = λ g p → refl
  }

-- The reciprocal action here is an *abstract copy* of the site
-- permutation and the pairing is syntactic equality; it is not
-- the physical U^{-T} action on a reciprocal wavevector lattice.
-- Constant band energy is a unit-test fixture, not band physics.

module DASHI.Mathematics.Symmetry.CrystalAtomic369TypedSeparationExact where

-- Cross-owner typed integration: an atomic index is not a crystal site,
-- and atomic valence does not automatically determine a crystal structure.
-- Attribution: existing AtomicPeriodicTable369GenerativeExact and the
-- IUCr classical crystal-symmetry classification remain source owners.
-- No postulates or specimen/quantum calculation is asserted.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic
import DASHI.Mathematics.Symmetry.CrystalClassificationSevenFourteenExact as Crystal
import DASHI.Mathematics.Symmetry.CrystalPointGroup32CatalogExact as PG

record DecoratedCrystalSite : Set where
  constructor decoratedCrystalSite
  field
    atom : Atomic.AtomicIndex
    fractionalSiteLabel : Nat
    occupancyLabel : Nat
open DecoratedCrystalSite public

-- Chemical-element identity depends on the proton number, not a
-- crystallographic site label, lattice class, or an electronic occupation
-- coordinate invented for this adapter.
sameElement : DecoratedCrystalSite → DecoratedCrystalSite → Set
sameElement x y = Atomic.ElementEquivalent (atom x) (atom y)

sameSiteLabel : DecoratedCrystalSite → DecoratedCrystalSite → Set
sameSiteLabel x y = fractionalSiteLabel x ≡ fractionalSiteLabel y

record IndexedCrystalModel : Set where
  constructor indexedCrystalModel
  field
    bravais : Crystal.BravaisType
    pointGroup : PG.CrystalPointGroup
    site : DecoratedCrystalSite
    elementIndex : Atomic.AtomicIndex
    siteElementWitness : Atomic.ElementEquivalent (atom site) elementIndex
    systemCompatibility : Crystal.systemOf bravais ≡ PG.crystalSystem pointGroup
open IndexedCrystalModel public

tetragonalModel :
  (a : Atomic.AtomicIndex) (position occupancy : Nat) →
  IndexedCrystalModel
tetragonalModel a position occupancy =
  indexedCrystalModel
    Crystal.tP
    PG.pg4OverMMM
    (decoratedCrystalSite a position occupancy)
    a
    refl
    refl

modelElementMatches :
  (a : Atomic.AtomicIndex) (position occupancy : Nat) →
  sameElement (site (tetragonalModel a position occupancy))
              (decoratedCrystalSite a position occupancy)
modelElementMatches a position occupancy = refl

-- This is a schema-level indexing witness only. It does not certify
-- actual fractional coordinates, allowed site stabilisers, Wyckoff
-- multiplicity, neutrality, Hamiltonian, spin, bonds, diffraction,
-- electron occupancy, or mineral structure.

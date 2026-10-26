module DASHI.Mathematics.Symmetry.CrystalRealizationConsumerContractExact where

-- A single consumer-facing gate shared by crystal classifications,
-- atomic basis decorations, direct/reciprocal lattice and Bloch models.
-- Classical point/space group, Fourier pairing and symmetry covariance
-- are external prior art. The novelty here is only a typed interface.
--
-- A point-group *label* never supplies an action or an observable.
-- The data below must be supplied by a genuine model/specimen source.
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Mathematics.Symmetry.CrystalClassificationSevenFourteenExact as Lattice
import DASHI.Mathematics.Symmetry.CrystalPointGroup32CatalogExact as Point
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic

record CrystalRealization
  (G Direct Reciprocal Site Energy : Set) : Set₁ where
  field
    bravais : Lattice.BravaisType
    pointGroup : Point.CrystalPointGroup
    classificationCompatible :
      Lattice.systemOf bravais ≡ Point.crystalSystem pointGroup

    identity : G
    compose : G → G → G
    directAction : G → Direct → Direct
    reciprocalAction : G → Reciprocal → Reciprocal

    directIdentity : (x : Direct) → directAction identity x ≡ x
    reciprocalIdentity :
      (k : Reciprocal) → reciprocalAction identity k ≡ k
    directCompose : (g h : G) (x : Direct) →
      directAction (compose g h) x ≡
      directAction g (directAction h x)
    reciprocalCompose : (g h : G) (k : Reciprocal) →
      reciprocalAction (compose g h) k ≡
      reciprocalAction g (reciprocalAction h k)

    -- Reciprocal covariance is not inferred from the two group laws.
    Pairing : Direct → Reciprocal → Set
    pairingCovariant : (g : G) (x : Direct) (k : Reciprocal) →
      Pairing x k → Pairing (directAction g x) (reciprocalAction g k)

    sitePosition : Site → Direct
    siteAtom : Site → Atomic.AtomicIndex
    siteAction : G → Site → Site
    sitePositionEquivariant : (g : G) (s : Site) →
      sitePosition (siteAction g s) ≡
      directAction g (sitePosition s)
    siteSpeciesPreserved : (g : G) (s : Site) →
      Atomic.ElementEquivalent
        (siteAtom (siteAction g s)) (siteAtom s)

    -- A consumer must *provide* a Bloch/physical covariance witness.
    BandEnergy : Reciprocal → Energy
    bandEnergyInvariant : (g : G) (k : Reciprocal) →
      BandEnergy (reciprocalAction g k) ≡ BandEnergy k

open CrystalRealization public

-- This is deliberately a conditional witness record, not an
-- implementation of a 230-space-group model. In particular:
-- * generic quantum bands need symmetry-compatible band relabelling;
-- * Seitz phase, spin, antiunitarity and degeneracies require extra data;
-- * a single BandEnergy is an optional scalar observable only.

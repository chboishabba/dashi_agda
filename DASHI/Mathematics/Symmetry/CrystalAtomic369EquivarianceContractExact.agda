module DASHI.Mathematics.Symmetry.CrystalAtomic369EquivarianceContractExact where

-- The minimal *obligation* for an atomic basis to possess a claimed
-- crystallographic symmetry, separately from an unlabelled lattice.
-- Uses native atomic identity by proton number, and separately records
-- site/occupancy preservation. The predicates are supplied by a
-- structure-specific proof, not manufactured from a point-group label.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atom
import DASHI.Mathematics.Symmetry.CrystalAtomic369TypedSeparationExact as Site

record LabelledBasisAction (G Position : Set) : Set₁ where
  field
    identity : G
    compose : G → G → G
    actPosition : G → Position → Position
    siteAtom : Position → Atom.AtomicIndex
    occupancy : Position → Nat
    identityPosition : (p : Position) → actPosition identity p ≡ p
    composePosition : (g h : G) (p : Position) →
      actPosition (compose g h) p ≡ actPosition g (actPosition h p)
    speciesPreserved : (g : G) (p : Position) →
      Atom.ElementEquivalent (siteAtom (actPosition g p)) (siteAtom p)
    occupancyPreserved : (g : G) (p : Position) →
      occupancy (actPosition g p) ≡ occupancy p
open LabelledBasisAction public

-- The complete species/occupancy contract can coexist with isotope
-- or spin distinctions, but does not automatically preserve them.
-- Space-group and fractional-position compatibility must be added
-- before calling this a physical crystal structure.

module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitModeSupport where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; length; lookup; deduplicate; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-deduplicate⁺; ∈-lookup)
open import Data.List.Relation.Unary.Any using (here; there; index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Unique.DecPropositional.Properties as UniqueDec
open import Data.Product using (Σ; _,_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (sym; cong)

import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Lattice
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport as LegacySupport
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitPairIncidences as Orbit

------------------------------------------------------------------------
-- Shared finite coordinates for the canonical-orbit incidence carrier.
--
-- This deliberately does not use `PhysicalCutoffModeSupport`'s old
-- triad-indexed incidence list.  Off-diagonal ordered inputs have already
-- been quotiented before endpoints are collected here.
------------------------------------------------------------------------

orbitEndpointSupport : List Orbit.OrbitPairIncidence → List Lattice.LatticeMode3
orbitEndpointSupport [] = []
orbitEndpointSupport (r ∷ rs) =
  Orbit.orbitIncidenceSource r ∷ Orbit.orbitIncidenceTarget r ∷
  orbitEndpointSupport rs

normalizedOrbitEndpointSupport :
  List Orbit.OrbitPairIncidence → List Lattice.LatticeMode3
normalizedOrbitEndpointSupport rs =
  deduplicate LegacySupport.latticeModeDecEq (orbitEndpointSupport rs)

normalizedOrbitEndpointSupportUnique :
  (rs : List Orbit.OrbitPairIncidence) →
  Unique (normalizedOrbitEndpointSupport rs)
normalizedOrbitEndpointSupportUnique rs =
  UniqueDec.deduplicate-! LegacySupport.latticeModeDecEq _

-- A duplicate-free finite list has injective coordinate lookup.  This is
-- stated locally because the physical carrier uses `Fin (length xs)` rather
-- than a vector conversion.
lookupUniqueInjective :
  {A : Set} → (xs : List A) → Unique xs →
  (i j : Fin (length xs)) → lookup xs i ≡ lookup xs j → i ≡ j
lookupUniqueInjective [] unique () () eq
lookupUniqueInjective (x ∷ xs) (AllPairs._∷_ x≉xs xsUnique) zero zero eq = refl
lookupUniqueInjective (x ∷ xs) (AllPairs._∷_ x≉xs xsUnique) zero (suc j) eq =
  contradiction eq (All.lookup x≉xs (∈-lookup j))
lookupUniqueInjective (x ∷ xs) (AllPairs._∷_ x≉xs xsUnique) (suc i) zero eq =
  contradiction (sym eq) (All.lookup x≉xs (∈-lookup i))
lookupUniqueInjective (x ∷ xs) (AllPairs._∷_ x≉xs xsUnique) (suc i) (suc j) eq =
  cong suc (lookupUniqueInjective xs xsUnique i j eq)

orbitSourceAppears :
  (r : Orbit.OrbitPairIncidence) → (rs : List Orbit.OrbitPairIncidence) →
  r ∈ rs → Orbit.orbitIncidenceSource r ∈ orbitEndpointSupport rs
orbitSourceAppears r (s ∷ rs) (here refl) = here refl
orbitSourceAppears r (s ∷ rs) (there r∈rs) =
  there (there (orbitSourceAppears r rs r∈rs))

orbitTargetAppears :
  (r : Orbit.OrbitPairIncidence) → (rs : List Orbit.OrbitPairIncidence) →
  r ∈ rs → Orbit.orbitIncidenceTarget r ∈ orbitEndpointSupport rs
orbitTargetAppears r (s ∷ rs) (here refl) = there (here refl)
orbitTargetAppears r (s ∷ rs) (there r∈rs) =
  there (there (orbitTargetAppears r rs r∈rs))

OrbitPhysicalCutoffIncidence : Nat → Nat → Set
OrbitPhysicalCutoffIncidence N R =
  Σ Orbit.OrbitPairIncidence
    (λ r → r ∈ Orbit.physicalCutoffOrbitPairIncidences N R)

physicalCutoffOrbitModeCoordinate : Nat → Nat → Set
physicalCutoffOrbitModeCoordinate N R =
  Fin (length (normalizedOrbitEndpointSupport
    (Orbit.physicalCutoffOrbitPairIncidences N R)))

orbitCoordinateMode :
  (N R : Nat) → physicalCutoffOrbitModeCoordinate N R → Lattice.LatticeMode3
orbitCoordinateMode N R i =
  lookup (normalizedOrbitEndpointSupport
    (Orbit.physicalCutoffOrbitPairIncidences N R)) i

orbitCoordinateModeInjective :
  (N R : Nat) →
  (i j : physicalCutoffOrbitModeCoordinate N R) →
  orbitCoordinateMode N R i ≡ orbitCoordinateMode N R j → i ≡ j
orbitCoordinateModeInjective N R i j =
  lookupUniqueInjective
    (normalizedOrbitEndpointSupport
      (Orbit.physicalCutoffOrbitPairIncidences N R))
    (normalizedOrbitEndpointSupportUnique
      (Orbit.physicalCutoffOrbitPairIncidences N R)) i j

orbitSourceCoordinate :
  (N R : Nat) → OrbitPhysicalCutoffIncidence N R →
  physicalCutoffOrbitModeCoordinate N R
orbitSourceCoordinate N R (r , r∈) =
  index (∈-deduplicate⁺ LegacySupport.latticeModeDecEq
    (orbitSourceAppears r (Orbit.physicalCutoffOrbitPairIncidences N R) r∈))

orbitTargetCoordinate :
  (N R : Nat) → OrbitPhysicalCutoffIncidence N R →
  physicalCutoffOrbitModeCoordinate N R
orbitTargetCoordinate N R (r , r∈) =
  index (∈-deduplicate⁺ LegacySupport.latticeModeDecEq
    (orbitTargetAppears r (Orbit.physicalCutoffOrbitPairIncidences N R) r∈))

orbitSourceCoordinateCorrect :
  (N R : Nat) → (r : OrbitPhysicalCutoffIncidence N R) →
  Orbit.orbitIncidenceSource (Data.Product.proj₁ r) ≡
  orbitCoordinateMode N R (orbitSourceCoordinate N R r)
orbitSourceCoordinateCorrect N R (r , r∈) =
  lookup-index (∈-deduplicate⁺ LegacySupport.latticeModeDecEq
    (orbitSourceAppears r (Orbit.physicalCutoffOrbitPairIncidences N R) r∈))

orbitTargetCoordinateCorrect :
  (N R : Nat) → (r : OrbitPhysicalCutoffIncidence N R) →
  Orbit.orbitIncidenceTarget (Data.Product.proj₁ r) ≡
  orbitCoordinateMode N R (orbitTargetCoordinate N R r)
orbitTargetCoordinateCorrect N R (r , r∈) =
  lookup-index (∈-deduplicate⁺ LegacySupport.latticeModeDecEq
    (orbitTargetAppears r (Orbit.physicalCutoffOrbitPairIncidences N R) r∈))

-- Keep the membership proof with each occurrence when indexing the operator
-- fold.  The same endpoint pair may occur more than once (notably in a
-- diagonal orbit), so this is intentionally an occurrence list.
liftOrbitIndexedMembership :
  (rs : List Orbit.OrbitPairIncidence) →
  List (Σ Orbit.OrbitPairIncidence (λ r → r ∈ rs))
liftOrbitIndexedMembership [] = []
liftOrbitIndexedMembership (r ∷ rs) =
  (r , here refl) ∷
  map
    (λ { (s , s∈) → s , there s∈ })
    (liftOrbitIndexedMembership rs)

physicalCutoffOrbitIndexedIncidences :
  (N R : Nat) → List (OrbitPhysicalCutoffIncidence N R)
physicalCutoffOrbitIndexedIncidences N R =
  liftOrbitIndexedMembership (Orbit.physicalCutoffOrbitPairIncidences N R)

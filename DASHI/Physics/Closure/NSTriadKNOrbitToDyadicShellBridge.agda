module DASHI.Physics.Closure.NSTriadKNOrbitToDyadicShellBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Oleg Kiriukhin; DASHI repository contributors.
-- Title: "Orbit-to-exact-shell and dyadic-shell comparison programme".
-- Venue/year: arXiv:2604.12188v1 and DASHI formal development, 2026.
-- DOI: 10.48550/arXiv.2604.12188; the bridge is DASHI-original.
-- Uses: the full octahedral orbit carrier, exact Euclidean shells, dyadic
-- shell fibres, orbit cardinality at most 48, and the seven physical
-- geometry classes.
-- Relationship: isolates every multiplicity and normalization needed to
-- transport a raw orbit-row theorem to the repository's dyadic shell
-- carrier. No lossless orbit-to-shell identification is assumed.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityCommutatorProgram as Helical

record OrbitDyadicShellCarrier
    {c o m s r : Level} : Set (lsuc (c ⊔ o ⊔ m ⊔ s ⊔ r)) where
  field
    Cutoff : Set c
    Orbit : Set o
    Mode : Set m
    State : Set s
    Scalar : Set r

    zero : Scalar
    add : Scalar → Scalar → Scalar
    leq : Scalar → Scalar → Set r

    orbitOf : Mode → Orbit
    orbitRepresentative : Orbit → Mode
    orbitCardinality : Orbit → Nat
    exactShellRadiusSquared : Orbit → Nat
    dyadicShellIndex : Orbit → Nat

    rawOrbitKernelMagnitude : Cutoff → State → Orbit → Orbit → Scalar
    exactShellKernelMagnitude : Cutoff → State → Nat → Nat → Scalar
    dyadicShellKernelMagnitude : Cutoff → State → Nat → Nat → Scalar

    orbitRowSum : Cutoff → State → Orbit → Scalar
    exactShellRowSum : Cutoff → State → Nat → Scalar
    dyadicShellRowSum : Cutoff → State → Nat → Scalar

open OrbitDyadicShellCarrier public

record OrbitToDyadicShellBridge
    {c o m s r : Level}
    (C : OrbitDyadicShellCarrier {c} {o} {m} {s} {r}) :
    Set (lsuc (c ⊔ o ⊔ m ⊔ s ⊔ r)) where
  field
    everyOrbitLiesInOneExactShell : Set
    everyExactShellLiesInOneDyadicShell : Set
    fullOctahedralOrbitCardinalityBound :
      ∀ orbit → orbitCardinality C orbit ≤ 48

    orbitMultiplicityConstant exactToDyadicOverlapConstant : Nat

    orbitKernelToExactShellMajorant :
      ∀ cutoff state orbit sourceOrbit → Set r
    exactShellToDyadicShellMajorant :
      ∀ cutoff state outputShell sourceShell → Set r

    rawOrbitRowToExactShellRow :
      ∀ cutoff state orbit →
      leq C
        (orbitRowSum C cutoff state orbit)
        (exactShellRowSum C cutoff state
          (exactShellRadiusSquared C orbit))

    exactShellRowToDyadicShellRow :
      ∀ cutoff state orbit →
      leq C
        (exactShellRowSum C cutoff state
          (exactShellRadiusSquared C orbit))
        (dyadicShellRowSum C cutoff state
          (dyadicShellIndex C orbit))

    orbitCardinalityNormalizationTracked : Set
    orderedRealityMateMultiplicityTracked : Set
    zeroModeExclusionTracked : Set
    cubicVersusEuclideanCutoffTracked : Set

    classifyOrbitTriad : Orbit → Orbit → Orbit → Helical.GeometricClass
    sevenGeometryClassesExhaustive : Set
    sevenGeometryClassesDisjoint : Set
    classwiseRowSumsReassemble : Set

open OrbitToDyadicShellBridge public

orbitToDyadicShellBridgeRepresented : Bool
orbitToDyadicShellBridgeRepresented = true

orbitToDyadicShellBridgeRepresentedIsTrue :
  orbitToDyadicShellBridgeRepresented ≡ true
orbitToDyadicShellBridgeRepresentedIsTrue = refl

orbitToDyadicShellBridgeClosed : Bool
orbitToDyadicShellBridgeClosed = false

orbitToDyadicShellBridgeClosedIsFalse :
  orbitToDyadicShellBridgeClosed ≡ false
orbitToDyadicShellBridgeClosedIsFalse = refl

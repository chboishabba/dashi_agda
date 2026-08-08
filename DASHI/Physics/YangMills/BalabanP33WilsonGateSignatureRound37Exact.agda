module DASHI.Physics.YangMills.BalabanP33WilsonGateSignatureRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Enrich the existing duplicate-free Wilson ownership carrier with the
-- multiscale signature required by Gate I.  Every one of the fifteen nonempty
-- subset atoms retains its polynomial degree, placement orbit, transport
-- depth, background-defect order, unique charge owner, locality radius, sign
-- status, and open dependency.  No scalar envelope erases these observers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanP33WilsonAtomOwnershipExact as Atom

------------------------------------------------------------------------
-- Placement orbits are calculated at the subset-combinatorics level.  The
-- physical covariant-prefix action may refine these classes, so the signature
-- stores that remaining dependency explicitly.
------------------------------------------------------------------------

data PlacementOrbit : Set where
  singletonOrbit adjacentPairOrbit oppositePairOrbit
    tripleOrbit quarticOrbit : PlacementOrbit

data BackgroundDefectOrder : Set where
  firstOrder secondOrder thirdOrder fourthOrder : BackgroundDefectOrder

data DependencyStatus : Set where
  eulerLagrangeOpen finiteYoungClosed deepRemainderClosed
    physicalOrbitIntertwinerOpen : DependencyStatus

placementOrbit : Atom.WilsonSubsetAtom → PlacementOrbit
placementOrbit Atom.singleton0 = singletonOrbit
placementOrbit Atom.singleton1 = singletonOrbit
placementOrbit Atom.singleton2 = singletonOrbit
placementOrbit Atom.singleton3 = singletonOrbit
placementOrbit Atom.pair01 = adjacentPairOrbit
placementOrbit Atom.pair02 = oppositePairOrbit
placementOrbit Atom.pair03 = adjacentPairOrbit
placementOrbit Atom.pair12 = adjacentPairOrbit
placementOrbit Atom.pair13 = oppositePairOrbit
placementOrbit Atom.pair23 = adjacentPairOrbit
placementOrbit Atom.triple012 = tripleOrbit
placementOrbit Atom.triple013 = tripleOrbit
placementOrbit Atom.triple023 = tripleOrbit
placementOrbit Atom.triple123 = tripleOrbit
placementOrbit Atom.quartic0123 = quarticOrbit

transportDepth : Atom.WilsonSubsetAtom → Nat
transportDepth Atom.singleton0 = 1
transportDepth Atom.singleton1 = 1
transportDepth Atom.singleton2 = 1
transportDepth Atom.singleton3 = 1
transportDepth Atom.pair01 = 2
transportDepth Atom.pair02 = 2
transportDepth Atom.pair03 = 2
transportDepth Atom.pair12 = 2
transportDepth Atom.pair13 = 2
transportDepth Atom.pair23 = 2
transportDepth Atom.triple012 = 3
transportDepth Atom.triple013 = 3
transportDepth Atom.triple023 = 3
transportDepth Atom.triple123 = 3
transportDepth Atom.quartic0123 = 4

backgroundDefectOrder : Atom.WilsonSubsetAtom → BackgroundDefectOrder
backgroundDefectOrder Atom.singleton0 = firstOrder
backgroundDefectOrder Atom.singleton1 = firstOrder
backgroundDefectOrder Atom.singleton2 = firstOrder
backgroundDefectOrder Atom.singleton3 = firstOrder
backgroundDefectOrder Atom.pair01 = secondOrder
backgroundDefectOrder Atom.pair02 = secondOrder
backgroundDefectOrder Atom.pair03 = secondOrder
backgroundDefectOrder Atom.pair12 = secondOrder
backgroundDefectOrder Atom.pair13 = secondOrder
backgroundDefectOrder Atom.pair23 = secondOrder
backgroundDefectOrder Atom.triple012 = thirdOrder
backgroundDefectOrder Atom.triple013 = thirdOrder
backgroundDefectOrder Atom.triple023 = thirdOrder
backgroundDefectOrder Atom.triple123 = thirdOrder
backgroundDefectOrder Atom.quartic0123 = fourthOrder

localityRadius : Atom.WilsonSubsetAtom → Nat
localityRadius Atom.singleton0 = 1
localityRadius Atom.singleton1 = 1
localityRadius Atom.singleton2 = 1
localityRadius Atom.singleton3 = 1
localityRadius Atom.pair01 = 2
localityRadius Atom.pair02 = 2
localityRadius Atom.pair03 = 2
localityRadius Atom.pair12 = 2
localityRadius Atom.pair13 = 2
localityRadius Atom.pair23 = 2
localityRadius Atom.triple012 = 3
localityRadius Atom.triple013 = 3
localityRadius Atom.triple023 = 3
localityRadius Atom.triple123 = 3
localityRadius Atom.quartic0123 = 4

dependencyStatus : Atom.WilsonSubsetAtom → DependencyStatus
dependencyStatus Atom.singleton0 = eulerLagrangeOpen
dependencyStatus Atom.singleton1 = eulerLagrangeOpen
dependencyStatus Atom.singleton2 = eulerLagrangeOpen
dependencyStatus Atom.singleton3 = eulerLagrangeOpen
dependencyStatus Atom.pair01 = finiteYoungClosed
dependencyStatus Atom.pair02 = finiteYoungClosed
dependencyStatus Atom.pair03 = finiteYoungClosed
dependencyStatus Atom.pair12 = finiteYoungClosed
dependencyStatus Atom.pair13 = finiteYoungClosed
dependencyStatus Atom.pair23 = finiteYoungClosed
dependencyStatus Atom.triple012 = deepRemainderClosed
dependencyStatus Atom.triple013 = deepRemainderClosed
dependencyStatus Atom.triple023 = deepRemainderClosed
dependencyStatus Atom.triple123 = deepRemainderClosed
dependencyStatus Atom.quartic0123 = deepRemainderClosed

record GateISignature : Set where
  constructor gate-i-signature
  field
    atom : Atom.WilsonSubsetAtom
    degree : Atom.AtomDegree
    orbit : PlacementOrbit
    transport : Nat
    defectOrder : BackgroundDefectOrder
    chargeOwner : Atom.BudgetOwner
    radius : Nat
    signStatus : Atom.SignStatus
    dependency : DependencyStatus

open GateISignature public

signature : Atom.WilsonSubsetAtom → GateISignature
signature subset =
  gate-i-signature
    subset
    (Atom.atomDegree subset)
    (placementOrbit subset)
    (transportDepth subset)
    (backgroundDefectOrder subset)
    (Atom.owner subset)
    (localityRadius subset)
    (Atom.signStatus subset)
    (dependencyStatus subset)

singletonSignature : GateISignature
singletonSignature = signature Atom.singleton0

pairSignature : GateISignature
pairSignature = signature Atom.pair01

singletonIsLowerDegreeButOpen :
  degree singletonSignature ≡ Atom.degree1
  × dependency singletonSignature ≡ eulerLagrangeOpen
  × signStatus singletonSignature ≡ Atom.curvatureSensitive
singletonIsLowerDegreeButOpen = refl , refl , refl

pairIsHigherDegreeButFiniteClosed :
  degree pairSignature ≡ Atom.degree2
  × dependency pairSignature ≡ finiteYoungClosed
  × signStatus pairSignature ≡ Atom.youngControlled
pairIsHigherDegreeButFiniteClosed = refl , refl , refl

oppositePairOrbitIsDistinguished :
  orbit (signature Atom.pair02) ≡ oppositePairOrbit
  × orbit (signature Atom.pair01) ≡ adjacentPairOrbit
oppositePairOrbitIsDistinguished = refl , refl

record GateISignatureBoundary : Set where
  constructor gate-i-signature-boundary
  field
    allFiniteObserversRetained : Bool
    allFiniteObserversRetainedIsTrue : allFiniteObserversRetained ≡ true
    lowerPolynomialDegreeMeansEasierSignControl : Bool
    lowerPolynomialDegreeMeansEasierSignControlIsFalse :
      lowerPolynomialDegreeMeansEasierSignControl ≡ false
    physicalPrefixActionProvesTheseOrbitClasses : Bool
    physicalPrefixActionProvesTheseOrbitClassesIsFalse :
      physicalPrefixActionProvesTheseOrbitClasses ≡ false

canonicalGateISignatureBoundary : GateISignatureBoundary
canonicalGateISignatureBoundary =
  gate-i-signature-boundary true refl false refl false refl

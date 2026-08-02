module DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeCoordinatesExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Dec; yes; no; Not; _∈_; pair; PositiveBond; elements; complete)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicEndpointBlockPredicateExact as Endpoint

------------------------------------------------------------------------
-- Concrete periodic tree-gauge coordinate indices.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions",
-- Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press; open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- A periodic BFS parent edge is undirected geometrically but DASHI stores bond
-- variables in positive orientation.  The conversion below chooses the bond at
-- the parent when the parent-to-child direction is positive and the bond at the
-- child when it is negative.  Filtering the complete periodic bond enumeration
-- against these tree bonds produces the canonical off-tree coordinate labels.
--
-- This is exact finite gauge combinatorics.  Identifying this tree gauge with
-- Bałaban's selected background gauge or Faddeev--Popov slice remains a separate
-- physical theorem.
------------------------------------------------------------------------

positiveBondOfAdjacentBlocks :
  ∀ {n} →
  Periodic.PeriodicBlock n → Periodic.PeriodicBlock n →
  PositiveBond (suc n)
positiveBondOfAdjacentBlocks left right
  with Adjacency.directionOfBlocks left right
... | pair axis true = pair left axis
... | pair axis false = pair right axis

positiveBondOfParentEdge :
  ∀ {n} → Periodic.ParentEdge n → PositiveBond (suc n)
positiveBondOfParentEdge edge =
  positiveBondOfAdjacentBlocks
    (Periodic.parent edge) (Periodic.child edge)

treePositiveBonds :
  ∀ {n} → Periodic.PeriodicTree n → List (PositiveBond (suc n))
treePositiveBonds [] = []
treePositiveBonds (edge ∷ edges) =
  positiveBondOfParentEdge edge ∷ treePositiveBonds edges

TreeBond :
  ∀ {n} → Periodic.PeriodicTree n → PositiveBond (suc n) → Set
TreeBond tree bond = bond ∈ treePositiveBonds tree

OffTreeBond :
  ∀ {n} → Periodic.PeriodicTree n → PositiveBond (suc n) → Set
OffTreeBond tree bond = Not (TreeBond tree bond)

treeBondDecidable :
  ∀ {n} (tree : Periodic.PeriodicTree n) bond →
  Dec (TreeBond tree bond)
treeBondDecidable {n} tree bond =
  Endpoint.membershipDecidable
    (Endpoint.positiveBondDecidableEquality (suc n))
    bond (treePositiveBonds tree)

offTreeBondDecidable :
  ∀ {n} (tree : Periodic.PeriodicTree n) bond →
  Dec (OffTreeBond tree bond)
offTreeBondDecidable tree bond with treeBondDecidable tree bond
... | yes treeMembership = no (λ notTree → notTree treeMembership)
... | no notTree = yes notTree

offTreePositiveBonds :
  ∀ {n} → Periodic.PeriodicTree n → List (PositiveBond (suc n))
offTreePositiveBonds {n} tree =
  Support.filterDec
    (OffTreeBond tree)
    (offTreeBondDecidable tree)
    (elements (Support.positiveBondFinite (suc n)))

offTreePositiveBondsSound :
  ∀ {n} (tree : Periodic.PeriodicTree n) bond →
  bond ∈ offTreePositiveBonds tree →
  OffTreeBond tree bond
offTreePositiveBondsSound tree bond =
  Support.filterDecSound (offTreeBondDecidable tree)

offTreePositiveBondsComplete :
  ∀ {n} (tree : Periodic.PeriodicTree n) bond →
  OffTreeBond tree bond →
  bond ∈ offTreePositiveBonds tree
offTreePositiveBondsComplete {n} tree bond offTree =
  Support.filterDecComplete
    (offTreeBondDecidable tree)
    (complete (Support.positiveBondFinite (suc n)) bond)
    offTree

data TreeOrOffTree {n}
    (tree : Periodic.PeriodicTree n)
    (bond : PositiveBond (suc n)) : Set where
  inTree : TreeBond tree bond → TreeOrOffTree tree bond
  offTree : OffTreeBond tree bond → TreeOrOffTree tree bond

treeOrOffTree :
  ∀ {n} (tree : Periodic.PeriodicTree n)
    (bond : PositiveBond (suc n)) →
  TreeOrOffTree tree bond
treeOrOffTree tree bond with treeBondDecidable tree bond
... | yes membership = inTree membership
... | no notMembership = offTree notMembership

TreeGaugeCoordinate :
  ∀ {n} → Periodic.PeriodicTree n → Set
TreeGaugeCoordinate {n} tree =
  Σ (PositiveBond (suc n)) (OffTreeBond tree)

coordinateBond :
  ∀ {n} {tree : Periodic.PeriodicTree n} →
  TreeGaugeCoordinate tree → PositiveBond (suc n)
coordinateBond (bond , isOffTree) = bond

coordinateOffTree :
  ∀ {n} {tree : Periodic.PeriodicTree n}
    (coordinate : TreeGaugeCoordinate tree) →
  OffTreeBond tree (coordinateBond coordinate)
coordinateOffTree (bond , isOffTree) = isOffTree

record CertifiedPeriodicTreeGaugeCoordinates
    (n : Nat) : Set₁ where
  field
    tree : Periodic.PeriodicTree n

    ParentEdgesAdjacent : Periodic.PeriodicTree n → Set
    parentEdgesAdjacent : ParentEdgesAdjacent tree

    SpanningTree : Periodic.PeriodicTree n → Set
    spanningTree : SpanningTree tree

    GaugeConditionMatchesTreeCoordinates :
      List (PositiveBond (suc n)) → Set

    gaugeConditionMatchesTreeCoordinates :
      GaugeConditionMatchesTreeCoordinates (offTreePositiveBonds tree)

open CertifiedPeriodicTreeGaugeCoordinates public

periodicTreePositiveOrientationLevel : ProofLevel
periodicTreePositiveOrientationLevel = computed

periodicOffTreeBondDecisionLevel : ProofLevel
periodicOffTreeBondDecisionLevel = machineChecked

periodicOffTreeCoordinateEnumerationLevel : ProofLevel
periodicOffTreeCoordinateEnumerationLevel = machineChecked

physicalBFSParentAdjacencyInputsLevel : ProofLevel
physicalBFSParentAdjacencyInputsLevel = conditional

physicalTreeGaugeSpanningInputsLevel : ProofLevel
physicalTreeGaugeSpanningInputsLevel = conditional

physicalBackgroundGaugeTreeCoordinateEquivalenceInputsLevel : ProofLevel
physicalBackgroundGaugeTreeCoordinateEquivalenceInputsLevel = conditional

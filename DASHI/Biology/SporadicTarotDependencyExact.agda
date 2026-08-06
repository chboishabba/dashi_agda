module DASHI.Biology.SporadicTarotDependencyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Fin using (Fin)

------------------------------------------------------------------------
-- Sources:
--
-- J. H. Conway, R. T. Curtis, S. P. Norton, R. A. Parker, R. A. Wilson,
-- Atlas of Finite Groups, Oxford University Press, 1985,
-- ISBN 0-19-853199-0; no DOI assigned to the book.
--
-- R. T. Curtis, Natural Constructions of the Mathieu Groups,
-- Mathematical Proceedings of the Cambridge Philosophical Society 106
-- (1989), 423-429, DOI 10.1017/S0305004100068158.
--
-- The module separates the mathematical inventory from a twenty-two-slot
-- Tarot/Kabbalistic correspondence.  A symbolic card may be meaningful inside
-- a declared correspondence without becoming a finite simple group.
------------------------------------------------------------------------

data SporadicGroup : Set where
  M11 : SporadicGroup
  M12 : SporadicGroup
  M22 : SporadicGroup
  M23 : SporadicGroup
  M24 : SporadicGroup

  J2 : SporadicGroup
  HS : SporadicGroup
  McL : SporadicGroup
  Suz : SporadicGroup
  Co1 : SporadicGroup
  Co2 : SporadicGroup
  Co3 : SporadicGroup

  Fi22 : SporadicGroup
  Fi23 : SporadicGroup
  Fi24Prime : SporadicGroup
  He : SporadicGroup
  HN : SporadicGroup
  Th : SporadicGroup
  BabyMonster : SporadicGroup
  Monster : SporadicGroup

  J1 : SporadicGroup
  J3 : SporadicGroup
  J4 : SporadicGroup
  ONean : SporadicGroup
  Ru : SporadicGroup
  Ly : SporadicGroup

allSporadicGroups : List SporadicGroup
allSporadicGroups =
  M11 ∷ M12 ∷ M22 ∷ M23 ∷ M24
  ∷ J2 ∷ HS ∷ McL ∷ Suz ∷ Co1 ∷ Co2 ∷ Co3
  ∷ Fi22 ∷ Fi23 ∷ Fi24Prime ∷ He ∷ HN ∷ Th ∷ BabyMonster ∷ Monster
  ∷ J1 ∷ J3 ∷ J4 ∷ ONean ∷ Ru ∷ Ly
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

sporadicInventoryCount : Nat
sporadicInventoryCount = listCount allSporadicGroups

sporadicInventoryCountIsTwentySix : sporadicInventoryCount ≡ 26
sporadicInventoryCountIsTwentySix = refl

------------------------------------------------------------------------
-- ATLAS family partition: 5 Mathieu, 7 Leech-lattice, 8 Monster-section,
-- and 6 pariah groups.
------------------------------------------------------------------------

data SporadicFamily : Set where
  mathieuFamily : SporadicFamily
  leechLatticeFamily : SporadicFamily
  monsterSectionFamily : SporadicFamily
  pariahFamily : SporadicFamily

sporadicFamily : SporadicGroup → SporadicFamily
sporadicFamily M11 = mathieuFamily
sporadicFamily M12 = mathieuFamily
sporadicFamily M22 = mathieuFamily
sporadicFamily M23 = mathieuFamily
sporadicFamily M24 = mathieuFamily

sporadicFamily J2 = leechLatticeFamily
sporadicFamily HS = leechLatticeFamily
sporadicFamily McL = leechLatticeFamily
sporadicFamily Suz = leechLatticeFamily
sporadicFamily Co1 = leechLatticeFamily
sporadicFamily Co2 = leechLatticeFamily
sporadicFamily Co3 = leechLatticeFamily

sporadicFamily Fi22 = monsterSectionFamily
sporadicFamily Fi23 = monsterSectionFamily
sporadicFamily Fi24Prime = monsterSectionFamily
sporadicFamily He = monsterSectionFamily
sporadicFamily HN = monsterSectionFamily
sporadicFamily Th = monsterSectionFamily
sporadicFamily BabyMonster = monsterSectionFamily
sporadicFamily Monster = monsterSectionFamily

sporadicFamily J1 = pariahFamily
sporadicFamily J3 = pariahFamily
sporadicFamily J4 = pariahFamily
sporadicFamily ONean = pariahFamily
sporadicFamily Ru = pariahFamily
sporadicFamily Ly = pariahFamily

mathieuGroups : List SporadicGroup
mathieuGroups = M11 ∷ M12 ∷ M22 ∷ M23 ∷ M24 ∷ []

leechLatticeGroups : List SporadicGroup
leechLatticeGroups =
  J2 ∷ HS ∷ McL ∷ Suz ∷ Co1 ∷ Co2 ∷ Co3 ∷ []

monsterSectionGroups : List SporadicGroup
monsterSectionGroups =
  Fi22 ∷ Fi23 ∷ Fi24Prime ∷ He ∷ HN ∷ Th ∷ BabyMonster ∷ Monster ∷ []

pariahGroups : List SporadicGroup
pariahGroups = J1 ∷ J3 ∷ J4 ∷ ONean ∷ Ru ∷ Ly ∷ []

mathieuCountIsFive : listCount mathieuGroups ≡ 5
mathieuCountIsFive = refl

leechLatticeCountIsSeven : listCount leechLatticeGroups ≡ 7
leechLatticeCountIsSeven = refl

monsterSectionCountIsEight : listCount monsterSectionGroups ≡ 8
monsterSectionCountIsEight = refl

pariahCountIsSix : listCount pariahGroups ≡ 6
pariahCountIsSix = refl

familyCountsSumToTwentySix : 5 + 7 + 8 + 6 ≡ 26
familyCountsSumToTwentySix = refl

------------------------------------------------------------------------
-- There are exactly three mathematical Conway sporadic constructors.  Co4 may
-- be retained only as a synthetic card label unless a distinct mathematical
-- referent is supplied.
------------------------------------------------------------------------

data ConwaySporadic : Set where
  conwayOne : ConwaySporadic
  conwayTwo : ConwaySporadic
  conwayThree : ConwaySporadic

conwaySporadics : List ConwaySporadic
conwaySporadics = conwayOne ∷ conwayTwo ∷ conwayThree ∷ []

conwaySporadicCountIsThree : listCount conwaySporadics ≡ 3
conwaySporadicCountIsThree = refl

data Optional (A : Set) : Set where
  none : Optional A
  some : A → Optional A

data ConwayCardLabel : Set where
  Co1Card : ConwayCardLabel
  Co2Card : ConwayCardLabel
  Co3Card : ConwayCardLabel
  Co4SyntheticCard : ConwayCardLabel

conwayCardReferent : ConwayCardLabel → Optional ConwaySporadic
conwayCardReferent Co1Card = some conwayOne
conwayCardReferent Co2Card = some conwayTwo
conwayCardReferent Co3Card = some conwayThree
conwayCardReferent Co4SyntheticCard = none

co4HasNoConwaySporadicReferent :
  conwayCardReferent Co4SyntheticCard ≡ none
co4HasNoConwaySporadicReferent = refl

------------------------------------------------------------------------
-- Mathieu natural permutation degrees and the 22-point Witt-design block
-- arithmetic.  The block equation is kept division-free:
--
--   77 * C(6,3) = C(22,3),
--   77 * 20     = 1540.
------------------------------------------------------------------------

data MathieuGroup : Set where
  mathieu11 : MathieuGroup
  mathieu12 : MathieuGroup
  mathieu22 : MathieuGroup
  mathieu23 : MathieuGroup
  mathieu24 : MathieuGroup

naturalPermutationDegree : MathieuGroup → Nat
naturalPermutationDegree mathieu11 = 11
naturalPermutationDegree mathieu12 = 12
naturalPermutationDegree mathieu22 = 22
naturalPermutationDegree mathieu23 = 23
naturalPermutationDegree mathieu24 = 24

mathieuDegreeTable :
  naturalPermutationDegree mathieu11 ≡ 11
  × naturalPermutationDegree mathieu12 ≡ 12
  × naturalPermutationDegree mathieu22 ≡ 22
  × naturalPermutationDegree mathieu23 ≡ 23
  × naturalPermutationDegree mathieu24 ≡ 24
mathieuDegreeTable = refl , refl , refl , refl , refl

sixChooseThree : Nat
sixChooseThree = 20

twentyTwoChooseThree : Nat
twentyTwoChooseThree = 1540

wittBlockCount : Nat
wittBlockCount = 77

wittBlockEquation :
  wittBlockCount * sixChooseThree ≡ twentyTwoChooseThree
wittBlockEquation = refl

------------------------------------------------------------------------
-- A twenty-two-card deck is a symbolic observation or curated selection, not
-- a complete one-to-one sporadic inventory.  The missing correspondence rule
-- is represented as data rather than guessed from card aesthetics.
------------------------------------------------------------------------

Arcana22 : Set
Arcana22 = Fin 22

arcanaCount : Nat
arcanaCount = 22

inventoryMinusArcanaCount : Nat
inventoryMinusArcanaCount = sporadicInventoryCount ∸ arcanaCount

inventoryMinusArcanaCountIsFour : inventoryMinusArcanaCount ≡ 4
inventoryMinusArcanaCountIsFour = refl

twentySixIsNotTwentyTwo : 26 ≡ 22 → ⊥
twentySixIsNotTwentyTwo ()

data CorrespondenceAuthority : Set where
  mathematicalReferentAuthority : CorrespondenceAuthority
  declaredSymbolicAuthority : CorrespondenceAuthority
  undefinedCorrespondenceAuthority : CorrespondenceAuthority

record TarotCorrespondenceRule : Set where
  constructor tarotCorrespondenceRule
  field
    assignArcana : SporadicGroup → Arcana22
    rationale : SporadicGroup → String
    authority : SporadicGroup → CorrespondenceAuthority

record MathematicalValidityLedger : Set where
  constructor mathematicalValidityLedger
  field
    completeSporadicInventoryUsed : Bool
    syntheticLabelsSeparated : Bool
    ordersAndActionsExternallyChecked : Bool
    familyClassificationChecked : Bool

record SymbolicCorrespondenceLedger : Set where
  constructor symbolicCorrespondenceLedger
  field
    correspondenceRuleDeclared : Bool
    mergedFibresDeclared : Bool
    omittedGroupsDeclared : Bool
    syntheticCardsDeclared : Bool

------------------------------------------------------------------------
-- Typed dependency graph replacing a misleading linear tower.
------------------------------------------------------------------------

data DependencyNode : Set where
  fourElementCarrierNode : DependencyNode
  semigroupAxiomNode : DependencyNode
  monoidAxiomNode : DependencyNode
  groupAxiomNode : DependencyNode
  abelianGroupAxiomNode : DependencyNode
  f2VectorSpaceNode : DependencyNode
  affinePlaneNode : DependencyNode
  projectivePlaneNode : DependencyNode
  fanoPlaneNode : DependencyNode
  steinerS3622Node : DependencyNode
  binaryGolayCodeNode : DependencyNode
  mathieu24Node : DependencyNode
  leechLatticeNode : DependencyNode
  conwayGroupsNode : DependencyNode
  moonshineVOANode : DependencyNode
  monsterGroupNode : DependencyNode
  tarotArcanaNode : DependencyNode

data DependencyEdgeKind : Set where
  sameCarrierStrongerAxioms : DependencyEdgeKind
  sameObjectDifferentPresentation : DependencyEdgeKind
  constructionInput : DependencyEdgeKind
  automorphismGroup : DependencyEdgeKind
  stabiliserOrQuotient : DependencyEdgeKind
  subgroupOrSubquotient : DependencyEdgeKind
  vertexOperatorAlgebraBridge : DependencyEdgeKind
  historicalAssociation : DependencyEdgeKind
  symbolicCorrespondence : DependencyEdgeKind

record TypedDependencyEdge : Set where
  constructor typedDependencyEdge
  field
    source : DependencyNode
    target : DependencyNode
    kind : DependencyEdgeKind

open TypedDependencyEdge public

canonicalDependencyGraph : List TypedDependencyEdge
canonicalDependencyGraph =
  typedDependencyEdge fourElementCarrierNode semigroupAxiomNode sameCarrierStrongerAxioms
  ∷ typedDependencyEdge semigroupAxiomNode monoidAxiomNode sameCarrierStrongerAxioms
  ∷ typedDependencyEdge monoidAxiomNode groupAxiomNode sameCarrierStrongerAxioms
  ∷ typedDependencyEdge groupAxiomNode abelianGroupAxiomNode sameCarrierStrongerAxioms
  ∷ typedDependencyEdge abelianGroupAxiomNode f2VectorSpaceNode sameCarrierStrongerAxioms
  ∷ typedDependencyEdge f2VectorSpaceNode affinePlaneNode constructionInput
  ∷ typedDependencyEdge affinePlaneNode projectivePlaneNode constructionInput
  ∷ typedDependencyEdge projectivePlaneNode fanoPlaneNode sameObjectDifferentPresentation
  ∷ typedDependencyEdge fanoPlaneNode steinerS3622Node historicalAssociation
  ∷ typedDependencyEdge steinerS3622Node binaryGolayCodeNode constructionInput
  ∷ typedDependencyEdge binaryGolayCodeNode mathieu24Node automorphismGroup
  ∷ typedDependencyEdge binaryGolayCodeNode leechLatticeNode constructionInput
  ∷ typedDependencyEdge leechLatticeNode conwayGroupsNode stabiliserOrQuotient
  ∷ typedDependencyEdge leechLatticeNode moonshineVOANode vertexOperatorAlgebraBridge
  ∷ typedDependencyEdge moonshineVOANode monsterGroupNode automorphismGroup
  ∷ typedDependencyEdge monsterGroupNode tarotArcanaNode symbolicCorrespondence
  ∷ []

canonicalDependencyEdgeCount : Nat
canonicalDependencyEdgeCount = listCount canonicalDependencyGraph

canonicalDependencyEdgeCountIsSixteen :
  canonicalDependencyEdgeCount ≡ 16
canonicalDependencyEdgeCountIsSixteen = refl

record SporadicTarotBoundary : Set where
  constructor sporadicTarotBoundary
  field
    twentyTwoArcanaAreCompleteSporadicInventory : Bool
    twentyTwoArcanaAreCompleteSporadicInventoryIsFalse :
      twentyTwoArcanaAreCompleteSporadicInventory ≡ false

    syntheticCo4IsSporadicSimpleGroup : Bool
    syntheticCo4IsSporadicSimpleGroupIsFalse :
      syntheticCo4IsSporadicSimpleGroup ≡ false

    symbolicCorrespondenceCreatesMathematicalReferent : Bool
    symbolicCorrespondenceCreatesMathematicalReferentIsFalse :
      symbolicCorrespondenceCreatesMathematicalReferent ≡ false

    everyTowerEdgeIsCanonicalImplication : Bool
    everyTowerEdgeIsCanonicalImplicationIsFalse :
      everyTowerEdgeIsCanonicalImplication ≡ false

    typedDependencyGraphRetainsEdgeAuthority : Bool
    typedDependencyGraphRetainsEdgeAuthorityIsTrue :
      typedDependencyGraphRetainsEdgeAuthority ≡ true

open SporadicTarotBoundary public

canonicalSporadicTarotBoundary : SporadicTarotBoundary
canonicalSporadicTarotBoundary =
  sporadicTarotBoundary
    false refl
    false refl
    false refl
    false refl
    true refl

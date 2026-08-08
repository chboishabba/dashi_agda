module DASHI.Biology.SporadicTarotDependencyExact where

open import DASHI.Core.Prelude
open import DASHI.Core.Optional public
open import Agda.Builtin.String using (String)
open import Data.Fin using (Fin)

-- Sources:
-- J. H. Conway, R. T. Curtis, S. P. Norton, R. A. Parker, R. A. Wilson,
-- Atlas of Finite Groups, Oxford University Press, 1985,
-- ISBN 0-19-853199-0; no DOI assigned.
-- R. T. Curtis, Natural Constructions of the Mathieu Groups,
-- Mathematical Proceedings of the Cambridge Philosophical Society 106
-- (1989), 423-429, DOI 10.1017/S0305004100068158.

data SporadicGroup : Set where
  M11 M12 M22 M23 M24 : SporadicGroup
  J2 HS McL Suz Co1 Co2 Co3 : SporadicGroup
  Fi22 Fi23 Fi24Prime He HN Th BabyMonster Monster : SporadicGroup
  J1 J3 J4 ONean Ru Ly : SporadicGroup

allSporadicGroups : List SporadicGroup
allSporadicGroups =
  M11 ∷ M12 ∷ M22 ∷ M23 ∷ M24
  ∷ J2 ∷ HS ∷ McL ∷ Suz ∷ Co1 ∷ Co2 ∷ Co3
  ∷ Fi22 ∷ Fi23 ∷ Fi24Prime ∷ He ∷ HN ∷ Th ∷ BabyMonster ∷ Monster
  ∷ J1 ∷ J3 ∷ J4 ∷ ONean ∷ Ru ∷ Ly ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

sporadicInventoryCount : Nat
sporadicInventoryCount = listCount allSporadicGroups

sporadicInventoryCountIsTwentySix : sporadicInventoryCount ≡ 26
sporadicInventoryCountIsTwentySix = refl

data SporadicFamily : Set where
  mathieuFamily leechLatticeFamily monsterSectionFamily pariahFamily :
    SporadicFamily

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
leechLatticeGroups = J2 ∷ HS ∷ McL ∷ Suz ∷ Co1 ∷ Co2 ∷ Co3 ∷ []

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

data ConwaySporadic : Set where
  conwayOne conwayTwo conwayThree : ConwaySporadic

conwaySporadics : List ConwaySporadic
conwaySporadics = conwayOne ∷ conwayTwo ∷ conwayThree ∷ []

conwaySporadicCountIsThree : listCount conwaySporadics ≡ 3
conwaySporadicCountIsThree = refl

data ConwayCardLabel : Set where
  Co1Card Co2Card Co3Card Co4SyntheticCard : ConwayCardLabel

conwayCardReferent : ConwayCardLabel → Optional ConwaySporadic
conwayCardReferent Co1Card = some conwayOne
conwayCardReferent Co2Card = some conwayTwo
conwayCardReferent Co3Card = some conwayThree
conwayCardReferent Co4SyntheticCard = none

co4HasNoConwaySporadicReferent :
  conwayCardReferent Co4SyntheticCard ≡ none
co4HasNoConwaySporadicReferent = refl

data MathieuGroup : Set where
  mathieu11 mathieu12 mathieu22 mathieu23 mathieu24 : MathieuGroup

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

wittBlockEquation : wittBlockCount * sixChooseThree ≡ twentyTwoChooseThree
wittBlockEquation = refl

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
  mathematicalReferentAuthority declaredSymbolicAuthority
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
    completeSporadicInventoryUsed syntheticLabelsSeparated
      ordersAndActionsExternallyChecked familyClassificationChecked : Bool

record SymbolicCorrespondenceLedger : Set where
  constructor symbolicCorrespondenceLedger
  field
    correspondenceRuleDeclared mergedFibresDeclared omittedGroupsDeclared
      syntheticCardsDeclared : Bool

data DependencyNode : Set where
  fourElementCarrierNode semigroupAxiomNode monoidAxiomNode groupAxiomNode
    abelianGroupAxiomNode f2VectorSpaceNode affinePlaneNode projectivePlaneNode
    fanoPlaneNode steinerS3622Node binaryGolayCodeNode mathieu24Node
    leechLatticeNode conwayGroupsNode moonshineVOANode monsterGroupNode
    tarotArcanaNode : DependencyNode

data DependencyEdgeKind : Set where
  sameCarrierStrongerAxioms sameObjectDifferentPresentation constructionInput
    automorphismGroup stabiliserOrQuotient subgroupOrSubquotient
    vertexOperatorAlgebraBridge historicalAssociation symbolicCorrespondence :
    DependencyEdgeKind

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

canonicalDependencyEdgeCountIsSixteen : canonicalDependencyEdgeCount ≡ 16
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
    false refl false refl false refl false refl true refl

module DASHI.Wikimedia.IbrahimJMathSecondOrderQidThirdOrderRelationsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimJMathematicsNumberOEISSecondOrderQidSnowballExact as Second
import DASHI.Wikimedia.IntegerSequenceRecurrenceTetrationSnowballExact as Recurrence
import DASHI.Wikimedia.Base369NumberTheoryNumerologyWrongTypeSnowballExact as WrongType
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- THIRD-ORDER RELATIONS FROM THE SECOND-ORDER QIDS.
--
-- This owner follows every new second-order identity far enough to classify
-- its next useful relation without inventing a new domain formalism.
------------------------------------------------------------------------

data ThirdOrderRole : Set where
  subclassRelation partRelation oppositeRelation studiesRelation subjectRelation
  formulaSymbolRelation externalIdentifierRelation ontologyFacetRelation
  repositoryReuseRelation unresolvedNextRelation : ThirdOrderRole

record ThirdOrderRelation : Set where
  constructor third-order-relation
  field
    sourceIdentity : String
    role : ThirdOrderRole
    target : String
    evidence : String
    repoSubstrateObserved : Bool
    createsFormalDependency : Bool
open ThirdOrderRelation public

------------------------------------------------------------------------
-- Q870797 modular form.
------------------------------------------------------------------------

modularFormToHolomorphic : ThirdOrderRelation
modularFormToHolomorphic = third-order-relation
  "Q870797 modular form"
  subclassRelation
  "holomorphic function"
  "Wikidata Q870797 subclasses holomorphic function and meromorphic function"
  true false

modularFormToModularGroup : ThirdOrderRelation
modularFormToModularGroup = third-order-relation
  "Q870797 modular form"
  formulaSymbolRelation
  "modular group / upper half-plane / congruence subgroup / integer matrix"
  "Q870797 defining-formula symbol roles explicitly expose these analytic/algebraic coordinates"
  true false

modularFormToIntegerCarrier : ThirdOrderRelation
modularFormToIntegerCarrier = third-order-relation
  "Q870797 modular form"
  formulaSymbolRelation
  "integer and set of integers"
  "Q870797 defining-formula symbols include integer and set of integers; this is a typed arithmetic coordinate, not a reduction of modular forms to integer arithmetic"
  true false

------------------------------------------------------------------------
-- Q874429 group theory.
------------------------------------------------------------------------

groupTheoryToAlgebra : ThirdOrderRelation
groupTheoryToAlgebra = third-order-relation
  "Q874429 group theory"
  partRelation
  "algebra"
  "Wikidata mathematics modelling records group theory as a branch of mathematics, part of algebra"
  true false

groupTheoryToGroup : ThirdOrderRelation
groupTheoryToGroup = third-order-relation
  "Q874429 group theory"
  subjectRelation
  "group"
  "Wikidata mathematics modelling records group theory as the study of group"
  true false

------------------------------------------------------------------------
-- Q837863 pure mathematics.
------------------------------------------------------------------------

pureMathToMathematics : ThirdOrderRelation
pureMathToMathematics = third-order-relation
  "Q837863 pure mathematics"
  subclassRelation
  "Q395 mathematics"
  "Q837863 is mathematics independent of application and subclasses mathematics"
  true false

pureMathOppositeApplied : ThirdOrderRelation
pureMathOppositeApplied = third-order-relation
  "Q837863 pure mathematics"
  oppositeRelation
  "applied mathematics"
  "Q837863 currently records applied mathematics as opposite-of"
  true false

------------------------------------------------------------------------
-- Q18450254 elementary number theory.
------------------------------------------------------------------------

elementaryNumberTheoryToModularArithmetic : ThirdOrderRelation
elementaryNumberTheoryToModularArithmetic = third-order-relation
  "Q18450254 elementary number theory"
  partRelation
  "modular arithmetic"
  "Wikidata modular-arithmetic item records modular arithmetic as part of elementary number theory"
  true false

------------------------------------------------------------------------
-- Q47007735 set of integers.
------------------------------------------------------------------------

setOfIntegersToInteger : ThirdOrderRelation
setOfIntegersToInteger = third-order-relation
  "Q47007735 set of integers"
  ontologyFacetRelation
  "Q12503 integer"
  "set-of-integers item has parts of class integer; element and carrier-set roles remain distinct"
  true false

setOfIntegersToZ3 : ThirdOrderRelation
setOfIntegersToZ3 = third-order-relation
  "Q47007735 set of integers"
  repositoryReuseRelation
  "DASHI NSIntegerFourierLattice = Z^3"
  "repo FourierMode is literally a triple of Agda integers; Q47007735 supplies the external identity of the coordinate carrier only"
  true false

------------------------------------------------------------------------
-- Q246672 mathematical object.
------------------------------------------------------------------------

mathematicalObjectToMathematics : ThirdOrderRelation
mathematicalObjectToMathematics = third-order-relation
  "Q246672 mathematical object"
  studiesRelation
  "Q395 mathematics"
  "Q246672 says mathematical objects are studied by mathematics and characterized by mathematical properties/cardinality"
  true false

------------------------------------------------------------------------
-- Q16317911 positive integer.
------------------------------------------------------------------------

positiveIntegerToA000027 : ThirdOrderRelation
positiveIntegerToA000027 = third-order-relation
  "Q16317911 positive integer"
  externalIdentifierRelation
  "OEIS A000027"
  "Wikidata directly attaches OEIS ID A000027 to the positive-integer concept"
  true false

------------------------------------------------------------------------
-- Coverage / next snowball.
------------------------------------------------------------------------

record ThirdOrderCoverage : Set where
  constructor third-order-coverage
  field
    modularFormAnalyticCoordinatesRetained : Bool
    groupTheoryAlgebraCoordinatesRetained : Bool
    pureVsAppliedAxisRetained : Bool
    elementaryNumberTheoryModularArithmeticRetained : Bool
    integerElementVsCarrierSetSeparated : Bool
    z3CoordinateCarrierCrossPollinated : Bool
    mathematicalObjectGeneralityRetained : Bool
    positiveIntegerOEISIdentifierRetained : Bool
    genericIntegerSequenceRecursionRoleRetained : Bool
    numberTheoryNumerologyWrongTypeRetained : Bool
    nextHighestAlpha : String
open ThirdOrderCoverage public

canonicalThirdOrderCoverage : ThirdOrderCoverage
canonicalThirdOrderCoverage = third-order-coverage
  true true true true true true true true true true
  "Weld Q870797's explicit integer/set-of-integers formula coordinates to the existing modular-form owners and Z^3 carrier, while preserving analytic modular transformation laws as the promotion gate"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data IntegerSymbolsMakeModularFormIntegerSequence : Set where
data GroupTheoryMakesEveryGroupMoonshine : Set where
data PureMathematicsMeansNoApplications : Set where
data IntegerElementEqualsIntegerCarrierSet : Set where
data MathematicalObjectQidCreatesObjectSemantics : Set where

integerSymbolsDoNotCollapseModularForm : IntegerSymbolsMakeModularFormIntegerSequence → ⊥
integerSymbolsDoNotCollapseModularForm ()

groupTheoryDoesNotCreateMoonshine : GroupTheoryMakesEveryGroupMoonshine → ⊥
groupTheoryDoesNotCreateMoonshine ()

pureMathLabelDoesNotProveNoApplications : PureMathematicsMeansNoApplications → ⊥
pureMathLabelDoesNotProveNoApplications ()

integerIsNotCarrierSet : IntegerElementEqualsIntegerCarrierSet → ⊥
integerIsNotCarrierSet ()

qidDoesNotCreateObjectSemantics : MathematicalObjectQidCreatesObjectSemantics → ⊥
qidDoesNotCreateObjectSemantics ()

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

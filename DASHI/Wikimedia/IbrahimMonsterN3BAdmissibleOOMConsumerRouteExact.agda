module DASHI.Wikimedia.IbrahimMonsterN3BAdmissibleOOMConsumerRouteExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFamilyRefinementKernelExact as Family
import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BScreenReceiptExact as Screen

------------------------------------------------------------------------
-- N(3B) ADMISSIBLE / OOM-AVOIDANCE CONSUMER ROUTE
--
-- Declared consumer:
--   which admissible D8 realization/fusion supplies the five-orbit action?
--
-- The current 17/17 character-table result is treated as a collision fibre:
-- the character observer retained all seventeen candidates and therefore does
-- not select a realization.  This does NOT authorize loading a richer whole
-- group or 78 x 78 matrix representation.  Instead, reopen only the next
-- consumer-relevant residual coordinate.
--
-- The exact FactorsThrough theorem below is deliberately about this declared
-- consumer model.  It proves that a heavy matrix payload is irrelevant once
-- the consumer answer is represented on the quotient/permutation surface.
-- It is not a proof that a particular real D8 <= N(3B) has already been found,
-- and it does not manufacture the real-group intersection D8 ∩ 3^(1+12)=1.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Consumer-indexed quotient model.
------------------------------------------------------------------------

data D8RealizationClass : Set where
  unresolvedD8 : D8RealizationClass
  selectedD8Class : D8RealizationClass

data MonsterFusionClass : Set where
  unresolvedFusion : MonsterFusionClass
  selectedFusionClass : MonsterFusionClass

record QuotientPermutationSurface : Set where
  constructor quotient-permutation-surface
  field
    d8Class : D8RealizationClass
    monsterFusion : MonsterFusionClass
    fiveOrbitPermutationCharacterRetained : Bool
open QuotientPermutationSurface public

record N3BSearchWorld : Set where
  constructor n3b-search-world
  field
    quotientSurface : QuotientPermutationSurface
    matrix78PayloadPresent : Bool
    fullGroupEnumerationPresent : Bool
open N3BSearchWorld public

data N3BConsumerQuery : Set where
  whichAdmissibleD8Fusion : N3BConsumerQuery

n3bConsumerQuestions : Query.InquiryQuestionFamily N3BSearchWorld N3BConsumerQuery
n3bConsumerQuestions = Query.inquiryQuestionFamily answer ask
  where
    answer : N3BConsumerQuery → Set
    answer whichAdmissibleD8Fusion = QuotientPermutationSurface

    ask : (query : N3BConsumerQuery) → N3BSearchWorld → answer query
    ask whichAdmissibleD8Fusion world = quotientSurface world

projectToQuotient : N3BSearchWorld → QuotientPermutationSurface
projectToQuotient = quotientSurface

declaredConsumerFactorsThroughProjection :
  Query.FactorsThrough n3bConsumerQuestions projectToQuotient whichAdmissibleD8Fusion
declaredConsumerFactorsThroughProjection =
  Query.factorsThrough (λ surface → surface) proof
  where
    proof :
      (world : N3BSearchWorld) →
      Query.ask n3bConsumerQuestions whichAdmissibleD8Fusion world
      ≡ projectToQuotient world
    proof world = refl

------------------------------------------------------------------------
-- 2. Admissible route and cost hyperfabric.
------------------------------------------------------------------------

data SearchRoute : Set where
  quotientPermutationRoute : SearchRoute
  matrix78Route : SearchRoute

data RouteAdmissible : SearchRoute → Set where
  quotientRouteAdmissible : RouteAdmissible quotientPermutationRoute
  matrixRouteAdmissible : RouteAdmissible matrix78Route

data RouteConsumerAdequate : SearchRoute → Set where
  quotientRouteAdequate : RouteConsumerAdequate quotientPermutationRoute
  matrixRouteAdequate : RouteConsumerAdequate matrix78Route

data RouteRefines : SearchRoute → SearchRoute → Set where
  quotientSelfRefines : RouteRefines quotientPermutationRoute quotientPermutationRoute
  matrixSelfRefines : RouteRefines matrix78Route matrix78Route
  quotientToMatrixRefinement : RouteRefines quotientPermutationRoute matrix78Route

routeDescriptionLength : SearchRoute → Nat
routeDescriptionLength quotientPermutationRoute = 1
routeDescriptionLength matrix78Route = 5

routeReference : SearchRoute → String
routeReference quotientPermutationRoute = "N(3B) quotient/permutation residual route"
routeReference matrix78Route = "N(3B) 78x78 matrix realization route"

n3bRouteProblem : MDL.ConsumerMDLProblem
n3bRouteProblem = MDL.consumerMDLProblem
  SearchRoute
  RouteAdmissible
  RouteConsumerAdequate
  routeDescriptionLength
  RouteRefines
  routeReference
  "ordinal engineering costs for the declared D8/fusion consumer only"
  "which admissible D8 realization/fusion supplies the five-orbit action?"

data CostAxis : Set where
  ramAxis : CostAxis
  matrixDimensionAxis : CostAxis
  groupEnumerationAxis : CostAxis
  candidateCountAxis : CostAxis
  proofDebtAxis : CostAxis

routeCost : CostAxis → SearchRoute → Nat
routeCost ramAxis quotientPermutationRoute = 1
routeCost ramAxis matrix78Route = 5
routeCost matrixDimensionAxis quotientPermutationRoute = 0
routeCost matrixDimensionAxis matrix78Route = 78
routeCost groupEnumerationAxis quotientPermutationRoute = 1
routeCost groupEnumerationAxis matrix78Route = 5
routeCost candidateCountAxis quotientPermutationRoute = 17
routeCost candidateCountAxis matrix78Route = 17
routeCost proofDebtAxis quotientPermutationRoute = 2
routeCost proofDebtAxis matrix78Route = 5

costAxisReference : CostAxis → String
costAxisReference ramAxis = "RAM"
costAxisReference matrixDimensionAxis = "matrix dimension"
costAxisReference groupEnumerationAxis = "group enumeration"
costAxisReference candidateCountAxis = "candidate count"
costAxisReference proofDebtAxis = "proof debt"

n3bCostHyperfabric : MDL.CostHyperfabric n3bRouteProblem
n3bCostHyperfabric = MDL.costHyperfabric CostAxis routeCost costAxisReference

------------------------------------------------------------------------
-- 3. Collision-local residual coordinates.
------------------------------------------------------------------------

data ResidualCoordinate : Set where
  actualD8ConjugacyClass : ResidualCoordinate
  inducedMonsterClassFusion : ResidualCoordinate
  fortyTwoBPower14To3B : ResidualCoordinate
  fortyTwoBPower7To6B : ResidualCoordinate
  fiveOrbitPermutationCharacter : ResidualCoordinate
  selectedActionIntertwinerReceipt : ResidualCoordinate

residualPriority : List ResidualCoordinate
residualPriority =
  actualD8ConjugacyClass
  ∷ inducedMonsterClassFusion
  ∷ fortyTwoBPower14To3B
  ∷ fortyTwoBPower7To6B
  ∷ fiveOrbitPermutationCharacter
  ∷ selectedActionIntertwinerReceipt
  ∷ []

currentScreenBoundary : Screen.FiveOrbitD4N3BScreenReceipt
currentScreenBoundary = Screen.currentFiveOrbitD4N3BScreenReceipt

observedCharacterTableCandidateCount : Nat
observedCharacterTableCandidateCount = 17

observedCharacterCompatibleCandidateCount : Nat
observedCharacterCompatibleCandidateCount = 17

------------------------------------------------------------------------
-- 4. WrongType / authority firewalls.
------------------------------------------------------------------------

data CharacterCollisionRequiresMatrixPayload : Set where
data QuotientRouteCreatesSelectedAction : Set where
data AbstractFactorsThroughCreatesRealD8Intersection : Set where

characterCollisionDoesNotRequireMatrixPayload :
  CharacterCollisionRequiresMatrixPayload → ⊥
characterCollisionDoesNotRequireMatrixPayload ()

quotientRouteDoesNotCreateSelectedAction :
  QuotientRouteCreatesSelectedAction → ⊥
quotientRouteDoesNotCreateSelectedAction ()

abstractFactorisationDoesNotCreateRealD8Intersection :
  AbstractFactorsThroughCreatesRealD8Intersection → ⊥
abstractFactorisationDoesNotCreateRealD8Intersection ()

------------------------------------------------------------------------
-- 5. Current boundary.
------------------------------------------------------------------------

record N3BOOMBoundary : Set where
  constructor n3b-oom-boundary
  field
    declaredConsumerFactorsThroughQuotient : Bool
    admissibleMDLProblemInstantiated : Bool
    costHyperfabricInstantiated : Bool
    characterObserverSeventeenWayCollision : Bool
    localResidualRefinementOnly : Bool
    residualOrderStartsWithD8ConjugacyClass : Bool
    matrix78RequiredForCurrentConsumer : Bool
    quotientRouteCreatesSelectedAction : Bool
    realGroupD8KernelIntersectionPaid : Bool
    selectedD8RealizationPaid : Bool
    exactSeventeenWorldResidualRowsRetained : Bool
    nextResidual : String
open N3BOOMBoundary public

currentN3BOOMBoundary : N3BOOMBoundary
currentN3BOOMBoundary = n3b-oom-boundary
  true true true true true true
  false false false false false
  "Consume the current 17/17 character-compatible fusion fibre without materializing the 78x78 representation. Compute actual D8 conjugacy class first; if collisions remain, reopen only induced Monster fusion, then 42B^14->3B, 42B^7->6B, five-orbit permutation character, and finally the selected action/intertwiner receipt. The abstract consumer factorisation is paid; the real-group D8 intersection and selected-action same-object weld remain independent obligations."

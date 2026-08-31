module DASHI.Culture.IntellectualReceptionAdmittedCounterfactualPathAlgebraExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / ADMITTED COUNTERFACTUAL PATH ALGEBRA
--
-- Thin specialization over the existing reception counterfactual hyperfabric.
-- The path constructors carry proof-relevant AdmittedStep receipts; therefore
-- concatenation composes only already-admitted legs.
--
-- Live PR #678 independently uses an indexed path + append pattern for proof
-- search dynamics.  That branch is inspiration only while open and is not
-- imported here.  The finite reception theorems below remain DASHI-owned.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible
import DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact as Stratum
import DASHI.Culture.IntellectualReceptionCounterfactualHyperfabricExact as Counterfactual

------------------------------------------------------------------------
-- 1. Indexed admitted paths.
------------------------------------------------------------------------

data AdmittedCounterfactualPath :
    Counterfactual.CounterfactualReceptionState →
    Counterfactual.CounterfactualReceptionState → Set where
  pathRefl :
    ∀ {state} →
    AdmittedCounterfactualPath state state

  pathStep :
    ∀ {start finish} →
    (move : Counterfactual.CounterfactualIntervention) →
    Admissible.AdmittedStep
      Counterfactual.counterfactualTransitionSystem
      move
      Counterfactual.ordinaryCounterfactual
      start →
    AdmittedCounterfactualPath
      (Counterfactual.applyIntervention move start)
      finish →
    AdmittedCounterfactualPath start finish

appendPath :
  ∀ {start middle finish} →
  AdmittedCounterfactualPath start middle →
  AdmittedCounterfactualPath middle finish →
  AdmittedCounterfactualPath start finish
appendPath pathRefl right = right
appendPath (pathStep move admitted rest) right =
  pathStep move admitted (appendPath rest right)

pathLength :
  ∀ {start finish} →
  AdmittedCounterfactualPath start finish → Nat
pathLength pathRefl = 0
pathLength (pathStep move admitted rest) = suc (pathLength rest)

------------------------------------------------------------------------
-- 2. Concrete admitted paths from the counterfactual owner.
------------------------------------------------------------------------

movementPrefix :
  AdmittedCounterfactualPath
    Counterfactual.seedState
    Counterfactual.movementIntermediate
movementPrefix =
  pathStep
    Counterfactual.shiftToMovementHistory
    Counterfactual.movementFirstAdmitted
    pathRefl

institutionAfterMovementSuffix :
  AdmittedCounterfactualPath
    Counterfactual.movementIntermediate
    Counterfactual.movementThenInstitution
institutionAfterMovementSuffix =
  pathStep
    Counterfactual.shiftRelationToInstitution
    Counterfactual.institutionAfterMovementAdmitted
    pathRefl

movementThenInstitutionPath :
  AdmittedCounterfactualPath
    Counterfactual.seedState
    Counterfactual.movementThenInstitution
movementThenInstitutionPath =
  appendPath movementPrefix institutionAfterMovementSuffix

institutionPrefix :
  AdmittedCounterfactualPath
    Counterfactual.seedState
    Counterfactual.institutionIntermediate
institutionPrefix =
  pathStep
    Counterfactual.shiftRelationToInstitution
    Counterfactual.institutionFirstAdmitted
    pathRefl

movementAfterInstitutionSuffix :
  AdmittedCounterfactualPath
    Counterfactual.institutionIntermediate
    Counterfactual.institutionThenMovement
movementAfterInstitutionSuffix =
  pathStep
    Counterfactual.shiftToMovementHistory
    Counterfactual.movementAfterInstitutionAdmitted
    pathRefl

institutionThenMovementPath :
  AdmittedCounterfactualPath
    Counterfactual.seedState
    Counterfactual.institutionThenMovement
institutionThenMovementPath =
  appendPath institutionPrefix movementAfterInstitutionSuffix

movementThenInstitutionHasLengthTwo :
  pathLength movementThenInstitutionPath ≡ 2
movementThenInstitutionHasLengthTwo = refl

institutionThenMovementHasLengthTwo :
  pathLength institutionThenMovementPath ≡ 2
institutionThenMovementHasLengthTwo = refl

------------------------------------------------------------------------
-- 3. Same admissibility trace does not recover path order.
--
-- Both canonical paths have exactly two admitted legs.  A consumer retaining
-- only that admitted/admitted trace cannot recover which intervention came first.
------------------------------------------------------------------------

data TwoLegAdmittedPath : Set where
  movementThenInstitutionTrace
  institutionThenMovementTrace
  : TwoLegAdmittedPath

data AdmissibilityTraceCode : Set where
  twoAdmittedLegs : AdmissibilityTraceCode

data OrderedPathCode : Set where
  movementBeforeInstitution
  institutionBeforeMovement
  : OrderedPathCode

admissibilityTrace : TwoLegAdmittedPath → AdmissibilityTraceCode
admissibilityTrace _ = twoAdmittedLegs

orderedPath : TwoLegAdmittedPath → OrderedPathCode
orderedPath movementThenInstitutionTrace = movementBeforeInstitution
orderedPath institutionThenMovementTrace = institutionBeforeMovement

orderedPathsDiffer :
  orderedPath movementThenInstitutionTrace
  ≡ orderedPath institutionThenMovementTrace → ⊥
orderedPathsDiffer ()

sameAdmissibilityTraceCannotRecoverPathOrder :
  INF.FactorsThrough admissibilityTrace orderedPath → ⊥
sameAdmissibilityTraceCannotRecoverPathOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      movementThenInstitutionTrace
      institutionThenMovementTrace
      refl
      orderedPathsDiffer)

------------------------------------------------------------------------
-- 4. Same exact future cone still does not recover the admitted path.
------------------------------------------------------------------------

pathFutureCone : TwoLegAdmittedPath → Stratum.FutureConeCode
pathFutureCone movementThenInstitutionTrace =
  Stratum.futureCone (Counterfactual.stratum Counterfactual.movementThenInstitution)
pathFutureCone institutionThenMovementTrace =
  Stratum.futureCone (Counterfactual.stratum Counterfactual.institutionThenMovement)

sameFutureConeAcrossCanonicalPaths :
  pathFutureCone movementThenInstitutionTrace
  ≡ pathFutureCone institutionThenMovementTrace
sameFutureConeAcrossCanonicalPaths = refl

sameExactFutureConeCannotRecoverAdmittedPathOrder :
  INF.FactorsThrough pathFutureCone orderedPath → ⊥
sameExactFutureConeCannotRecoverAdmittedPathOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      movementThenInstitutionTrace
      institutionThenMovementTrace
      sameFutureConeAcrossCanonicalPaths
      orderedPathsDiffer)

------------------------------------------------------------------------
-- 5. Same endpoint does not recover path length/history.
--
-- shiftRelationToInstitution is idempotent on the fine state: applying it once
-- or twice reaches definitionally the same state.  The admitted paths retain
-- different lengths, so endpoint equality is strictly coarser than path history.
------------------------------------------------------------------------

institutionTwice : Counterfactual.CounterfactualReceptionState
institutionTwice =
  Counterfactual.applyIntervention
    Counterfactual.shiftRelationToInstitution
    Counterfactual.institutionIntermediate

institutionTwiceIsInstitutionIntermediate :
  institutionTwice ≡ Counterfactual.institutionIntermediate
institutionTwiceIsInstitutionIntermediate = refl

institutionAgainAdmitted :
  Admissible.AdmittedStep
    Counterfactual.counterfactualTransitionSystem
    Counterfactual.shiftRelationToInstitution
    Counterfactual.ordinaryCounterfactual
    Counterfactual.institutionIntermediate
institutionAgainAdmitted = Admissible.admittedStep tt tt

oneRelationPath :
  AdmittedCounterfactualPath
    Counterfactual.seedState
    Counterfactual.institutionIntermediate
oneRelationPath = institutionPrefix

twoRelationPath :
  AdmittedCounterfactualPath
    Counterfactual.seedState
    institutionTwice
twoRelationPath =
  pathStep
    Counterfactual.shiftRelationToInstitution
    Counterfactual.institutionFirstAdmitted
    (pathStep
      Counterfactual.shiftRelationToInstitution
      institutionAgainAdmitted
      pathRefl)

oneRelationPathLength : pathLength oneRelationPath ≡ 1
oneRelationPathLength = refl

twoRelationPathLength : pathLength twoRelationPath ≡ 2
twoRelationPathLength = refl

data SameEndpointPathCase : Set where
  oneInstitutionShift twoInstitutionShifts : SameEndpointPathCase

data EndpointCode : Set where institutionalEndpoint : EndpointCode

data PathHistoryCode : Set where oneStepHistory twoStepHistory : PathHistoryCode

endpointCode : SameEndpointPathCase → EndpointCode
endpointCode _ = institutionalEndpoint

pathHistoryCode : SameEndpointPathCase → PathHistoryCode
pathHistoryCode oneInstitutionShift = oneStepHistory
pathHistoryCode twoInstitutionShifts = twoStepHistory

pathHistoriesDiffer :
  pathHistoryCode oneInstitutionShift
  ≡ pathHistoryCode twoInstitutionShifts → ⊥
pathHistoriesDiffer ()

sameEndpointCannotRecoverPathHistory :
  INF.FactorsThrough endpointCode pathHistoryCode → ⊥
sameEndpointCannotRecoverPathHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      oneInstitutionShift twoInstitutionShifts refl pathHistoriesDiffer)

------------------------------------------------------------------------
-- 6. Projection ladder.
--
-- These finite witnesses jointly separate endpoint, future cone,
-- admissibility trace and ordered path.  None is silently identified with the
-- next finer object.
------------------------------------------------------------------------

data PathProjectionLevel : Set where
  endpointLevel futureConeLevel admissibilityTraceLevel orderedPathLevel
  : PathProjectionLevel

data PathProjectionStrength : Set where
  endpointCoarse futureConeCoarse traceCoarse orderedPathFine
  : PathProjectionStrength

projectionStrength : PathProjectionLevel → PathProjectionStrength
projectionStrength endpointLevel = endpointCoarse
projectionStrength futureConeLevel = futureConeCoarse
projectionStrength admissibilityTraceLevel = traceCoarse
projectionStrength orderedPathLevel = orderedPathFine

------------------------------------------------------------------------
-- 7. No-promotion boundaries.
------------------------------------------------------------------------

data PathAlgebraPromotesActualHistory : Set where
data PathConcatenationPromotesPhysicalWorldline : Set where
data SameEndpointPromotesSameCausalHistory : Set where
data SameFutureConePromotesSamePath : Set where
data SameAdmissibilityTracePromotesSameInterventionOrder : Set where

aPathAlgebraDoesNotPromoteActualHistory : PathAlgebraPromotesActualHistory → ⊥
aPathAlgebraDoesNotPromoteActualHistory ()

pathConcatenationDoesNotPromotePhysicalWorldline :
  PathConcatenationPromotesPhysicalWorldline → ⊥
pathConcatenationDoesNotPromotePhysicalWorldline ()

sameEndpointDoesNotPromoteSameCausalHistory :
  SameEndpointPromotesSameCausalHistory → ⊥
sameEndpointDoesNotPromoteSameCausalHistory ()

sameFutureConeDoesNotPromoteSamePath : SameFutureConePromotesSamePath → ⊥
sameFutureConeDoesNotPromoteSamePath ()

sameTraceDoesNotPromoteSameInterventionOrder :
  SameAdmissibilityTracePromotesSameInterventionOrder → ⊥
sameTraceDoesNotPromoteSameInterventionOrder ()

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionAdmittedCounterfactualPathBoundary : Set where
  constructor intellectual-reception-admitted-counterfactual-path-boundary
  field
    admittedPathsComposeByConcatenation : Bool
    endpointDeterminesPathHistory : Bool
    exactFutureConeDeterminesOrderedPath : Bool
    admissibilityTraceDeterminesOrderedPath : Bool
    sameLengthDeterminesSamePath : Bool
    pathAlgebraIsActualHistory : Bool
    pathAlgebraIsPhysicalWorldline : Bool
    pathOrderRemainsFineInformation : Bool
    sourceAttributionBoundarySurvivesPathComposition : Bool

canonicalIntellectualReceptionAdmittedCounterfactualPathBoundary :
  IntellectualReceptionAdmittedCounterfactualPathBoundary
canonicalIntellectualReceptionAdmittedCounterfactualPathBoundary =
  intellectual-reception-admitted-counterfactual-path-boundary
    true false false false false false false true true

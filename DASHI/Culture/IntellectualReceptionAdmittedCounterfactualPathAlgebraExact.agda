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
--
-- Projection discipline:
--
--   endpoint
--   != future cone
--   != admissibility trace
--   != path length
--   != ordered admitted path.
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
-- 6. Same path length is also too coarse.
------------------------------------------------------------------------

data SameLengthPathCase : Set where
  movementInstitutionLengthTwo institutionMovementLengthTwo : SameLengthPathCase

data PathLengthCode : Set where lengthTwo : PathLengthCode

data FineOrderedLengthTwoPath : Set where
  movementInstitutionFine institutionMovementFine : FineOrderedLengthTwoPath

pathLengthCode : SameLengthPathCase → PathLengthCode
pathLengthCode _ = lengthTwo

fineOrderedLengthTwoPath : SameLengthPathCase → FineOrderedLengthTwoPath
fineOrderedLengthTwoPath movementInstitutionLengthTwo = movementInstitutionFine
fineOrderedLengthTwoPath institutionMovementLengthTwo = institutionMovementFine

sameLengthFinePathsDiffer :
  fineOrderedLengthTwoPath movementInstitutionLengthTwo
  ≡ fineOrderedLengthTwoPath institutionMovementLengthTwo → ⊥
sameLengthFinePathsDiffer ()

sameLengthCannotRecoverOrderedPath :
  INF.FactorsThrough pathLengthCode fineOrderedLengthTwoPath → ⊥
sameLengthCannotRecoverOrderedPath =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      movementInstitutionLengthTwo
      institutionMovementLengthTwo
      refl
      sameLengthFinePathsDiffer)

------------------------------------------------------------------------
-- 7. Projection ladder.
------------------------------------------------------------------------

data PathProjectionLevel : Set where
  endpointLevel futureConeLevel admissibilityTraceLevel pathLengthLevel orderedPathLevel
  : PathProjectionLevel

data PathProjectionStrength : Set where
  endpointCoarse futureConeCoarse traceCoarse lengthCoarse orderedPathFine
  : PathProjectionStrength

projectionStrength : PathProjectionLevel → PathProjectionStrength
projectionStrength endpointLevel = endpointCoarse
projectionStrength futureConeLevel = futureConeCoarse
projectionStrength admissibilityTraceLevel = traceCoarse
projectionStrength pathLengthLevel = lengthCoarse
projectionStrength orderedPathLevel = orderedPathFine

------------------------------------------------------------------------
-- 8. No-promotion boundaries.
------------------------------------------------------------------------

data PathAlgebraPromotesActualHistory : Set where
data PathConcatenationPromotesPhysicalWorldline : Set where
data SameEndpointPromotesSameCausalHistory : Set where
data SameFutureConePromotesSamePath : Set where
data SameAdmissibilityTracePromotesSameInterventionOrder : Set where
data SameLengthPromotesSamePath : Set where

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

sameLengthDoesNotPromoteSamePath : SameLengthPromotesSamePath → ⊥
sameLengthDoesNotPromoteSamePath ()

------------------------------------------------------------------------
-- 9. Canonical boundary.
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

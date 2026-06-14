module DASHI.Physics.Closure.NSAStationarityAuthorityReductionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS-A Abel triadic stationarity authority reduction boundary.
--
-- This receipt records the fail-closed route only.  A1 bounded Abel mass is
-- treated as already shaped; A3 stationarity authority is not promoted unless
-- four quantitative inputs are supplied together:
--
--   1. uniform Seregin/ESS rate;
--   2. harmonic pressure tail rate;
--   3. delta_r -> 0;
--   4. Abel summation closure.
--
-- The record is intentionally lightweight: it contains route evidence,
-- dependency flags, and promotion guards.  It proves no NS-A stationarity
-- theorem, no Clay Navier-Stokes theorem, and no terminal result.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Control-card text.

controlO : String
controlO =
  "O: record the NS-A Abel triadic stationarity authority reduction boundary"

controlR : String
controlR =
  "R: A1 bounded mass is shaped; A3 needs quantitative rate authority"

controlC : String
controlC =
  "C: no promotion without uniform Seregin/ESS, pressure-tail, delta, and Abel closure inputs"

controlS : String
controlS =
  "S: route receipt only, with explicit fail-closed status booleans"

controlL : String
controlL =
  "L: Abel-window stationarity must survive triadic summation"

controlP : String
controlP =
  "P: keep NS-A stationarity, Clay NS, and terminal promotion false"

controlG : String
controlG =
  "G: expose concrete route and blocker records for tests and downstream receipts"

controlF : String
controlF =
  "F: missing quantitative A3 closure remains the frontier"

------------------------------------------------------------------------
-- Route surface.

data NSAAuthorityRouteStep : Set where
  a1BoundedMassAlreadyShapedStep :
    NSAAuthorityRouteStep
  abelTriadicStationarityTargetStep :
    NSAAuthorityRouteStep
  uniformSereginESSRateDependencyStep :
    NSAAuthorityRouteStep
  harmonicPressureTailRateDependencyStep :
    NSAAuthorityRouteStep
  deltaRToZeroDependencyStep :
    NSAAuthorityRouteStep
  abelSummationClosureDependencyStep :
    NSAAuthorityRouteStep
  a3AuthorityReductionGateStep :
    NSAAuthorityRouteStep
  promotionGuardStep :
    NSAAuthorityRouteStep

canonicalNSAAuthorityRouteSteps :
  List NSAAuthorityRouteStep
canonicalNSAAuthorityRouteSteps =
  a1BoundedMassAlreadyShapedStep
  ∷ abelTriadicStationarityTargetStep
  ∷ uniformSereginESSRateDependencyStep
  ∷ harmonicPressureTailRateDependencyStep
  ∷ deltaRToZeroDependencyStep
  ∷ abelSummationClosureDependencyStep
  ∷ a3AuthorityReductionGateStep
  ∷ promotionGuardStep
  ∷ []

nsAAuthorityRouteStepCount : Nat
nsAAuthorityRouteStepCount =
  listLength canonicalNSAAuthorityRouteSteps

nsAAuthorityRouteStepCountIs8 :
  nsAAuthorityRouteStepCount ≡ 8
nsAAuthorityRouteStepCountIs8 =
  refl

routeText : String
routeText =
  "A1 bounded mass shaped -> A3 uniform Seregin/ESS rate + harmonic pressure tail rate + delta_r -> 0 + Abel summation closure -> stationarity authority reduction"

data A3StationarityDependency : Set where
  dependencyUniformSereginESSRate :
    A3StationarityDependency
  dependencyHarmonicPressureTailRate :
    A3StationarityDependency
  dependencyDeltaRToZero :
    A3StationarityDependency
  dependencyAbelSummationClosure :
    A3StationarityDependency

canonicalA3StationarityDependencies :
  List A3StationarityDependency
canonicalA3StationarityDependencies =
  dependencyUniformSereginESSRate
  ∷ dependencyHarmonicPressureTailRate
  ∷ dependencyDeltaRToZero
  ∷ dependencyAbelSummationClosure
  ∷ []

a3StationarityDependencyCount : Nat
a3StationarityDependencyCount =
  listLength canonicalA3StationarityDependencies

a3StationarityDependencyCountIs4 :
  a3StationarityDependencyCount ≡ 4
a3StationarityDependencyCountIs4 =
  refl

data AbelTriadicReductionClause : Set where
  triadicShellsUseAbelWindowWeights :
    AbelTriadicReductionClause
  stationarityDefectMeasuredAtReciprocalScales :
    AbelTriadicReductionClause
  pressureTailMustBeSummableAcrossWindows :
    AbelTriadicReductionClause
  sereginESSRateMustBeUniformAcrossWindows :
    AbelTriadicReductionClause
  deltaRLimitMustFeedTheA1MassWindow :
    AbelTriadicReductionClause
  abelSummationMustCloseWithoutExponentLoss :
    AbelTriadicReductionClause

canonicalAbelTriadicReductionClauses :
  List AbelTriadicReductionClause
canonicalAbelTriadicReductionClauses =
  triadicShellsUseAbelWindowWeights
  ∷ stationarityDefectMeasuredAtReciprocalScales
  ∷ pressureTailMustBeSummableAcrossWindows
  ∷ sereginESSRateMustBeUniformAcrossWindows
  ∷ deltaRLimitMustFeedTheA1MassWindow
  ∷ abelSummationMustCloseWithoutExponentLoss
  ∷ []

abelTriadicReductionClauseCount : Nat
abelTriadicReductionClauseCount =
  listLength canonicalAbelTriadicReductionClauses

abelTriadicReductionClauseCountIs6 :
  abelTriadicReductionClauseCount ≡ 6
abelTriadicReductionClauseCountIs6 =
  refl

------------------------------------------------------------------------
-- Concrete route flags.

NSAStationarityAuthorityReductionBoundaryRecorded : Bool
NSAStationarityAuthorityReductionBoundaryRecorded =
  true

A1BoundedMassAlreadyShaped : Bool
A1BoundedMassAlreadyShaped =
  true

A3StationarityDependsOnUniformSereginESSRate : Bool
A3StationarityDependsOnUniformSereginESSRate =
  true

A3StationarityDependsOnHarmonicPressureTailRate : Bool
A3StationarityDependsOnHarmonicPressureTailRate =
  true

A3StationarityDependsOnDeltaRToZero : Bool
A3StationarityDependsOnDeltaRToZero =
  true

A3StationarityDependsOnAbelSummationClosure : Bool
A3StationarityDependsOnAbelSummationClosure =
  true

AbelTriadicStationarityRouteRecorded : Bool
AbelTriadicStationarityRouteRecorded =
  true

A3AuthorityReductionRouteRecorded : Bool
A3AuthorityReductionRouteRecorded =
  true

------------------------------------------------------------------------
-- Blockers and fail-closed status.

data NSAAuthorityBlocker : Set where
  missingUniformSereginESSRate :
    NSAAuthorityBlocker
  missingHarmonicPressureTailRate :
    NSAAuthorityBlocker
  missingDeltaRToZeroBridge :
    NSAAuthorityBlocker
  missingAbelSummationClosure :
    NSAAuthorityBlocker
  missingA3StationarityAuthorityTheorem :
    NSAAuthorityBlocker
  missingClayNavierStokesPromotionAuthority :
    NSAAuthorityBlocker
  terminalPromotionForbidden :
    NSAAuthorityBlocker

canonicalNSAAuthorityBlockers :
  List NSAAuthorityBlocker
canonicalNSAAuthorityBlockers =
  missingUniformSereginESSRate
  ∷ missingHarmonicPressureTailRate
  ∷ missingDeltaRToZeroBridge
  ∷ missingAbelSummationClosure
  ∷ missingA3StationarityAuthorityTheorem
  ∷ missingClayNavierStokesPromotionAuthority
  ∷ terminalPromotionForbidden
  ∷ []

nsAAuthorityBlockerCount : Nat
nsAAuthorityBlockerCount =
  listLength canonicalNSAAuthorityBlockers

nsAAuthorityBlockerCountIs7 :
  nsAAuthorityBlockerCount ≡ 7
nsAAuthorityBlockerCountIs7 =
  refl

blockerName : NSAAuthorityBlocker → String
blockerName missingUniformSereginESSRate =
  "missingUniformSereginESSRate"
blockerName missingHarmonicPressureTailRate =
  "missingHarmonicPressureTailRate"
blockerName missingDeltaRToZeroBridge =
  "missingDeltaRToZeroBridge"
blockerName missingAbelSummationClosure =
  "missingAbelSummationClosure"
blockerName missingA3StationarityAuthorityTheorem =
  "missingA3StationarityAuthorityTheorem"
blockerName missingClayNavierStokesPromotionAuthority =
  "missingClayNavierStokesPromotionAuthority"
blockerName terminalPromotionForbidden =
  "terminalPromotionForbidden"

uniformSereginESSRateProved : Bool
uniformSereginESSRateProved =
  false

harmonicPressureTailRateProved : Bool
harmonicPressureTailRateProved =
  false

deltaRToZeroBridgeProved : Bool
deltaRToZeroBridgeProved =
  false

abelSummationClosureProved : Bool
abelSummationClosureProved =
  false

a3StationarityAuthorityReductionProved : Bool
a3StationarityAuthorityReductionProved =
  false

nsAStationarityPromoted : Bool
nsAStationarityPromoted =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

------------------------------------------------------------------------
-- Canonical record.

record NSAStationarityAuthorityReductionBoundary : Set where
  field
    routeSteps :
      List NSAAuthorityRouteStep
    routeStepsAreCanonical :
      routeSteps ≡ canonicalNSAAuthorityRouteSteps
    a3Dependencies :
      List A3StationarityDependency
    a3DependenciesAreCanonical :
      a3Dependencies ≡ canonicalA3StationarityDependencies
    abelTriadicClauses :
      List AbelTriadicReductionClause
    abelTriadicClausesAreCanonical :
      abelTriadicClauses ≡ canonicalAbelTriadicReductionClauses
    blockers :
      List NSAAuthorityBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSAAuthorityBlockers
    routeStepCountIs8 :
      nsAAuthorityRouteStepCount ≡ 8
    dependencyCountIs4 :
      a3StationarityDependencyCount ≡ 4
    abelTriadicClauseCountIs6 :
      abelTriadicReductionClauseCount ≡ 6
    blockerCountIs7 :
      nsAAuthorityBlockerCount ≡ 7
    boundaryRecorded :
      NSAStationarityAuthorityReductionBoundaryRecorded ≡ true
    a1BoundedMassShaped :
      A1BoundedMassAlreadyShaped ≡ true
    uniformSereginESSDependencyRecorded :
      A3StationarityDependsOnUniformSereginESSRate ≡ true
    harmonicPressureTailDependencyRecorded :
      A3StationarityDependsOnHarmonicPressureTailRate ≡ true
    deltaRToZeroDependencyRecorded :
      A3StationarityDependsOnDeltaRToZero ≡ true
    abelSummationClosureDependencyRecorded :
      A3StationarityDependsOnAbelSummationClosure ≡ true
    nsAStationarityStillFalse :
      nsAStationarityPromoted ≡ false
    nsClayStillFalse :
      nsClayPromoted ≡ false
    terminalStillFalse :
      terminalPromotion ≡ false

canonicalNSAStationarityAuthorityReductionBoundary :
  NSAStationarityAuthorityReductionBoundary
canonicalNSAStationarityAuthorityReductionBoundary =
  record
    { routeSteps =
        canonicalNSAAuthorityRouteSteps
    ; routeStepsAreCanonical =
        refl
    ; a3Dependencies =
        canonicalA3StationarityDependencies
    ; a3DependenciesAreCanonical =
        refl
    ; abelTriadicClauses =
        canonicalAbelTriadicReductionClauses
    ; abelTriadicClausesAreCanonical =
        refl
    ; blockers =
        canonicalNSAAuthorityBlockers
    ; blockersAreCanonical =
        refl
    ; routeStepCountIs8 =
        refl
    ; dependencyCountIs4 =
        refl
    ; abelTriadicClauseCountIs6 =
        refl
    ; blockerCountIs7 =
        refl
    ; boundaryRecorded =
        refl
    ; a1BoundedMassShaped =
        refl
    ; uniformSereginESSDependencyRecorded =
        refl
    ; harmonicPressureTailDependencyRecorded =
        refl
    ; deltaRToZeroDependencyRecorded =
        refl
    ; abelSummationClosureDependencyRecorded =
        refl
    ; nsAStationarityStillFalse =
        refl
    ; nsClayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }

NSAStationarityAuthorityReductionBoundaryRecordedIsTrue :
  NSAStationarityAuthorityReductionBoundaryRecorded ≡ true
NSAStationarityAuthorityReductionBoundaryRecordedIsTrue =
  refl

A1BoundedMassAlreadyShapedIsTrue :
  A1BoundedMassAlreadyShaped ≡ true
A1BoundedMassAlreadyShapedIsTrue =
  refl

A3StationarityUniformSereginESSRateDependencyIsTrue :
  A3StationarityDependsOnUniformSereginESSRate ≡ true
A3StationarityUniformSereginESSRateDependencyIsTrue =
  refl

A3StationarityHarmonicPressureTailRateDependencyIsTrue :
  A3StationarityDependsOnHarmonicPressureTailRate ≡ true
A3StationarityHarmonicPressureTailRateDependencyIsTrue =
  refl

A3StationarityDeltaRToZeroDependencyIsTrue :
  A3StationarityDependsOnDeltaRToZero ≡ true
A3StationarityDeltaRToZeroDependencyIsTrue =
  refl

A3StationarityAbelSummationClosureDependencyIsTrue :
  A3StationarityDependsOnAbelSummationClosure ≡ true
A3StationarityAbelSummationClosureDependencyIsTrue =
  refl

nsAStationarityPromotedIsFalse :
  nsAStationarityPromoted ≡ false
nsAStationarityPromotedIsFalse =
  refl

nsClayPromotedIsFalse :
  nsClayPromoted ≡ false
nsClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

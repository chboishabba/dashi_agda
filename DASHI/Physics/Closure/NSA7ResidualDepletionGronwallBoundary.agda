module DASHI.Physics.Closure.NSA7ResidualDepletionGronwallBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS A7 residual depletion / Gronwall boundary.
--
-- This is a lightweight, fail-closed receipt for the A7 step only.
-- It records the intended depletion route:
--
--   ∂t D_r + β D_r <= C D_r^(1+α)
--     -> Z = D_r^(-α)
--     -> Z' >= αβ Z - αC
--     -> smallness threshold D_r < (β / C)^(1 / α)
--     -> monotone decay of D_r
--     -> D_r -> 0
--     -> contradiction with persistent blowup.
--
-- It is intentionally standalone so it can typecheck directly under the
-- sprint timeout.  It proves no A7 theorem, no A8 local monotonicity, no
-- A9 CKN/BKM closure, no Navier-Stokes Clay result, and no terminal
-- promotion.

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

data ⊥ : Set where

------------------------------------------------------------------------
-- A7 proof clauses.

data A7GronwallClause : Set where
  differentialInequalityInput :
    A7GronwallClause
  positiveParametersAlphaBetaC :
    A7GronwallClause
  substitutionZEqualsDrToMinusAlpha :
    A7GronwallClause
  transformedLinearDifferentialInequality :
    A7GronwallClause
  thresholdBetaOverCToOneOverAlpha :
    A7GronwallClause
  subthresholdInitialDataImpliesMonotoneDecay :
    A7GronwallClause
  decayConvergesToZero :
    A7GronwallClause
  zeroResidualContradictsPersistentBlowup :
    A7GronwallClause

canonicalA7GronwallClauses :
  List A7GronwallClause
canonicalA7GronwallClauses =
  differentialInequalityInput
  ∷ positiveParametersAlphaBetaC
  ∷ substitutionZEqualsDrToMinusAlpha
  ∷ transformedLinearDifferentialInequality
  ∷ thresholdBetaOverCToOneOverAlpha
  ∷ subthresholdInitialDataImpliesMonotoneDecay
  ∷ decayConvergesToZero
  ∷ zeroResidualContradictsPersistentBlowup
  ∷ []

a7GronwallClauseCount : Nat
a7GronwallClauseCount =
  listLength canonicalA7GronwallClauses

a7GronwallClauseCountIs8 :
  a7GronwallClauseCount ≡ 8
a7GronwallClauseCountIs8 =
  refl

data A7GronwallTransformationStep : Set where
  step-rewriteAsDtDrLeqNegativeBetaDrPlusCDrPower :
    A7GronwallTransformationStep
  step-differentiateDrToMinusAlpha :
    A7GronwallTransformationStep
  step-cancelCommonPowerOfDr :
    A7GronwallTransformationStep
  step-obtainLinearLowerBoundForZPrime :
    A7GronwallTransformationStep
  step-integrateLinearComparison :
    A7GronwallTransformationStep

canonicalA7GronwallTransformationSteps :
  List A7GronwallTransformationStep
canonicalA7GronwallTransformationSteps =
  step-rewriteAsDtDrLeqNegativeBetaDrPlusCDrPower
  ∷ step-differentiateDrToMinusAlpha
  ∷ step-cancelCommonPowerOfDr
  ∷ step-obtainLinearLowerBoundForZPrime
  ∷ step-integrateLinearComparison
  ∷ []

a7GronwallTransformationStepCount : Nat
a7GronwallTransformationStepCount =
  listLength canonicalA7GronwallTransformationSteps

a7GronwallTransformationStepCountIs5 :
  a7GronwallTransformationStepCount ≡ 5
a7GronwallTransformationStepCountIs5 =
  refl

data A7ThresholdConsequence : Set where
  thresholdDefinesForwardInvariantSmallDataRegion :
    A7ThresholdConsequence
  thresholdDominatesNonlinearSourceTerm :
    A7ThresholdConsequence
  thresholdForcesNegativeDrDerivative :
    A7ThresholdConsequence
  thresholdIsCompatibleWithDepletionContradictionStrategy :
    A7ThresholdConsequence

canonicalA7ThresholdConsequences :
  List A7ThresholdConsequence
canonicalA7ThresholdConsequences =
  thresholdDefinesForwardInvariantSmallDataRegion
  ∷ thresholdDominatesNonlinearSourceTerm
  ∷ thresholdForcesNegativeDrDerivative
  ∷ thresholdIsCompatibleWithDepletionContradictionStrategy
  ∷ []

a7ThresholdConsequenceCount : Nat
a7ThresholdConsequenceCount =
  listLength canonicalA7ThresholdConsequences

a7ThresholdConsequenceCountIs4 :
  a7ThresholdConsequenceCount ≡ 4
a7ThresholdConsequenceCountIs4 =
  refl

------------------------------------------------------------------------
-- Downstream blockers and fail-closed promotion state.

data DownstreamA7Blocker : Set where
  blocker-a7-gronwall-depletion-theorem-unproved :
    DownstreamA7Blocker
  blocker-a8-full-local-defect-monotonicity-unproved :
    DownstreamA7Blocker
  blocker-a9-ckn-bkm-closure-unproved :
    DownstreamA7Blocker
  blocker-ns-clay-authority-unproved :
    DownstreamA7Blocker
  blocker-terminal-promotion-forbidden :
    DownstreamA7Blocker

canonicalDownstreamA7Blockers :
  List DownstreamA7Blocker
canonicalDownstreamA7Blockers =
  blocker-a7-gronwall-depletion-theorem-unproved
  ∷ blocker-a8-full-local-defect-monotonicity-unproved
  ∷ blocker-a9-ckn-bkm-closure-unproved
  ∷ blocker-ns-clay-authority-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

downstreamA7BlockerCount : Nat
downstreamA7BlockerCount =
  listLength canonicalDownstreamA7Blockers

downstreamA7BlockerCountIs5 :
  downstreamA7BlockerCount ≡ 5
downstreamA7BlockerCountIs5 =
  refl

A7ResidualDepletionGronwallProved : Bool
A7ResidualDepletionGronwallProved =
  false

A7ResidualDepletionGronwallProvedIsFalse :
  A7ResidualDepletionGronwallProved ≡ false
A7ResidualDepletionGronwallProvedIsFalse =
  refl

A8FullLocalDefectMonotonicityProved : Bool
A8FullLocalDefectMonotonicityProved =
  false

A8FullLocalDefectMonotonicityProvedIsFalse :
  A8FullLocalDefectMonotonicityProved ≡ false
A8FullLocalDefectMonotonicityProvedIsFalse =
  refl

A9CKNBKMClosureProved : Bool
A9CKNBKMClosureProved =
  false

A9CKNBKMClosureProvedIsFalse :
  A9CKNBKMClosureProved ≡ false
A9CKNBKMClosureProvedIsFalse =
  refl

NSClayPromotedFromA7 : Bool
NSClayPromotedFromA7 =
  false

NSClayPromotedFromA7IsFalse :
  NSClayPromotedFromA7 ≡ false
NSClayPromotedFromA7IsFalse =
  refl

TerminalPromotionFromA7 : Bool
TerminalPromotionFromA7 =
  false

TerminalPromotionFromA7IsFalse :
  TerminalPromotionFromA7 ≡ false
TerminalPromotionFromA7IsFalse =
  refl

------------------------------------------------------------------------
-- Canonical receipt boundary.

record NSA7ResidualDepletionGronwallBoundary : Set where
  field
    gronwallClauses :
      List A7GronwallClause
    gronwallClausesAreCanonical :
      gronwallClauses ≡ canonicalA7GronwallClauses
    transformationSteps :
      List A7GronwallTransformationStep
    transformationStepsAreCanonical :
      transformationSteps ≡ canonicalA7GronwallTransformationSteps
    thresholdConsequences :
      List A7ThresholdConsequence
    thresholdConsequencesAreCanonical :
      thresholdConsequences ≡ canonicalA7ThresholdConsequences
    downstreamBlockers :
      List DownstreamA7Blocker
    downstreamBlockersAreCanonical :
      downstreamBlockers ≡ canonicalDownstreamA7Blockers
    clauseCountIs8 :
      a7GronwallClauseCount ≡ 8
    transformationStepCountIs5 :
      a7GronwallTransformationStepCount ≡ 5
    thresholdConsequenceCountIs4 :
      a7ThresholdConsequenceCount ≡ 4
    blockerCountIs5 :
      downstreamA7BlockerCount ≡ 5
    a7StillFalse :
      A7ResidualDepletionGronwallProved ≡ false
    a8StillFalse :
      A8FullLocalDefectMonotonicityProved ≡ false
    a9StillFalse :
      A9CKNBKMClosureProved ≡ false
    nsClayStillFalse :
      NSClayPromotedFromA7 ≡ false
    terminalStillFalse :
      TerminalPromotionFromA7 ≡ false

canonicalNSA7ResidualDepletionGronwallBoundary :
  NSA7ResidualDepletionGronwallBoundary
canonicalNSA7ResidualDepletionGronwallBoundary =
  record
    { gronwallClauses =
        canonicalA7GronwallClauses
    ; gronwallClausesAreCanonical =
        refl
    ; transformationSteps =
        canonicalA7GronwallTransformationSteps
    ; transformationStepsAreCanonical =
        refl
    ; thresholdConsequences =
        canonicalA7ThresholdConsequences
    ; thresholdConsequencesAreCanonical =
        refl
    ; downstreamBlockers =
        canonicalDownstreamA7Blockers
    ; downstreamBlockersAreCanonical =
        refl
    ; clauseCountIs8 =
        refl
    ; transformationStepCountIs5 =
        refl
    ; thresholdConsequenceCountIs4 =
        refl
    ; blockerCountIs5 =
        refl
    ; a7StillFalse =
        refl
    ; a8StillFalse =
        refl
    ; a9StillFalse =
        refl
    ; nsClayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }

NSA7ResidualDepletionGronwallBoundaryRecorded : Bool
NSA7ResidualDepletionGronwallBoundaryRecorded =
  true

NSA7ResidualDepletionGronwallBoundaryRecordedIsTrue :
  NSA7ResidualDepletionGronwallBoundaryRecorded ≡ true
NSA7ResidualDepletionGronwallBoundaryRecordedIsTrue =
  refl

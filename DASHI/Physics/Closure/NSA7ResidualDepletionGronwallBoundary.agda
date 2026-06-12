module DASHI.Physics.Closure.NSA7ResidualDepletionGronwallBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS A7 residual depletion / Gronwall boundary.
--
-- This is a lightweight, fail-closed receipt for the A7 step only.
-- It records the intended depletion route consuming the exact A6 assembled
-- inequality surface:
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

a6ClosureBoundaryReference : String
a6ClosureBoundaryReference =
  "DASHI.Physics.Closure.NSA6A4BiasToLeakageClosureCompositeBoundary"

a8BoundaryReference : String
a8BoundaryReference =
  "DASHI.Physics.Closure.NSA8FullLocalDefectMonotonicityBoundary"

a9BoundaryReference : String
a9BoundaryReference =
  "DASHI.Physics.Closure.NSA9CKNBKMClosureBoundary"

a6ClosureConsumedRecorded : Bool
a6ClosureConsumedRecorded =
  true

------------------------------------------------------------------------
-- A7 proof clauses.

data A7GronwallClause : Set where
  importedA6DifferentialInequalityInput :
    A7GronwallClause
  positiveParametersAlphaBetaCEffective :
    A7GronwallClause
  smallnessThresholdDrLessThanBetaOverCEffToOneOverAlpha :
    A7GronwallClause
  thresholdMakesNonlinearSourceStrictlySubcritical :
    A7GronwallClause
  substitutionZEqualsDrToMinusAlpha :
    A7GronwallClause
  transformedLinearDifferentialInequality :
    A7GronwallClause
  gronwallComparisonForZPrimeWithPositiveSlope :
    A7GronwallClause
  forwardInvariantSubthresholdRegion :
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
  importedA6DifferentialInequalityInput
  ∷ positiveParametersAlphaBetaCEffective
  ∷ smallnessThresholdDrLessThanBetaOverCEffToOneOverAlpha
  ∷ thresholdMakesNonlinearSourceStrictlySubcritical
  ∷ substitutionZEqualsDrToMinusAlpha
  ∷ transformedLinearDifferentialInequality
  ∷ gronwallComparisonForZPrimeWithPositiveSlope
  ∷ forwardInvariantSubthresholdRegion
  ∷ subthresholdInitialDataImpliesMonotoneDecay
  ∷ decayConvergesToZero
  ∷ zeroResidualContradictsPersistentBlowup
  ∷ []

a7GronwallClauseCount : Nat
a7GronwallClauseCount =
  listLength canonicalA7GronwallClauses

a7GronwallClauseCountIs11 :
  a7GronwallClauseCount ≡ 11
a7GronwallClauseCountIs11 =
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
  thresholdCanBeRestatedAsCEffDrPowerAlphaLessThanBeta :
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
  ∷ thresholdCanBeRestatedAsCEffDrPowerAlphaLessThanBeta
  ∷ thresholdForcesNegativeDrDerivative
  ∷ thresholdIsCompatibleWithDepletionContradictionStrategy
  ∷ []

a7ThresholdConsequenceCount : Nat
a7ThresholdConsequenceCount =
  listLength canonicalA7ThresholdConsequences

a7ThresholdConsequenceCountIs5 :
  a7ThresholdConsequenceCount ≡ 5
a7ThresholdConsequenceCountIs5 =
  refl

data A7ThresholdClause : Set where
  thresholdUsesTheImportedA6ConstantCEff :
    A7ThresholdClause
  thresholdEqualsBetaOverCEffToOneOverAlpha :
    A7ThresholdClause
  thresholdRequiresAlphaPositiveAndBetaPositive :
    A7ThresholdClause
  thresholdProducesStrictDerivativeGap :
    A7ThresholdClause
  thresholdRegionIsForwardInvariantUnderComparison :
    A7ThresholdClause

canonicalA7ThresholdClauses : List A7ThresholdClause
canonicalA7ThresholdClauses =
  thresholdUsesTheImportedA6ConstantCEff
  ∷ thresholdEqualsBetaOverCEffToOneOverAlpha
  ∷ thresholdRequiresAlphaPositiveAndBetaPositive
  ∷ thresholdProducesStrictDerivativeGap
  ∷ thresholdRegionIsForwardInvariantUnderComparison
  ∷ []

a7ThresholdClauseCount : Nat
a7ThresholdClauseCount =
  listLength canonicalA7ThresholdClauses

a7ThresholdClauseCountIs5 :
  a7ThresholdClauseCount ≡ 5
a7ThresholdClauseCountIs5 =
  refl

a7GronwallThresholdTheoremText : String
a7GronwallThresholdTheoremText =
  "A7 candidate theorem grammar: import the A6 inequality ∂t D_r + β D_r <= C_eff D_r^(1+alpha) with α,β,C_eff > 0, impose the threshold D_r < (β / C_eff)^(1 / alpha) so that C_eff D_r^alpha < β, rewrite with Z = D_r^(-alpha), derive Z' >= alpha*beta*Z - alpha*C_eff, and conclude forward-invariant monotone decay D_r -> 0, contradicting persistent blowup."

a7ThresholdSummary : String
a7ThresholdSummary =
  "Exact threshold grammar: if 0 < D_r < (β / C_eff)^(1 / alpha), then C_eff D_r^(1+alpha) < β D_r, hence ∂t D_r < 0 and the subthreshold region is comparison-stable forward in time."

a7GronwallComparisonSummary : String
a7GronwallComparisonSummary =
  "Gronwall comparison grammar: after Z = D_r^(-alpha), the transformed inequality is Z' >= alpha*beta*Z - alpha*C_eff; linear comparison yields exponential lower growth for Z once above the equilibrium C_eff / beta, forcing D_r to decrease and eventually vanish."

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

downstreamA7BlockerName : DownstreamA7Blocker → String
downstreamA7BlockerName blocker-a7-gronwall-depletion-theorem-unproved =
  "missingA7ResidualDepletionGronwallTheorem"
downstreamA7BlockerName blocker-a8-full-local-defect-monotonicity-unproved =
  "missingA8FullLocalDefectMonotonicityTheorem"
downstreamA7BlockerName blocker-a9-ckn-bkm-closure-unproved =
  "missingA9CKNBKMClosureTheorem"
downstreamA7BlockerName blocker-ns-clay-authority-unproved =
  "missingNSClayAuthorityAfterA7A9"
downstreamA7BlockerName blocker-terminal-promotion-forbidden =
  "missingTerminalPromotionAuthorityAfterA7A9"

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
    thresholdClauses :
      List A7ThresholdClause
    thresholdClausesAreCanonical :
      thresholdClauses ≡ canonicalA7ThresholdClauses
    downstreamBlockers :
      List DownstreamA7Blocker
    downstreamBlockersAreCanonical :
      downstreamBlockers ≡ canonicalDownstreamA7Blockers
    clauseCountIs11 :
      a7GronwallClauseCount ≡ 11
    transformationStepCountIs5 :
      a7GronwallTransformationStepCount ≡ 5
    thresholdConsequenceCountIs5 :
      a7ThresholdConsequenceCount ≡ 5
    thresholdClauseCountIs5 :
      a7ThresholdClauseCount ≡ 5
    theoremText :
      String
    thresholdSummary :
      String
    gronwallComparisonSummary :
      String
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
    ; thresholdClauses =
        canonicalA7ThresholdClauses
    ; thresholdClausesAreCanonical =
        refl
    ; downstreamBlockers =
        canonicalDownstreamA7Blockers
    ; downstreamBlockersAreCanonical =
        refl
    ; clauseCountIs11 =
        refl
    ; transformationStepCountIs5 =
        refl
    ; thresholdConsequenceCountIs5 =
        refl
    ; thresholdClauseCountIs5 =
        refl
    ; theoremText =
        a7GronwallThresholdTheoremText
    ; thresholdSummary =
        a7ThresholdSummary
    ; gronwallComparisonSummary =
        a7GronwallComparisonSummary
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

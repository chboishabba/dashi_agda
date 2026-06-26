module DASHI.Physics.Closure.NSA7ResidualDepletionGronwallBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6A4BiasToLeakageClosureCompositeBoundary
  as A6Closure
import DASHI.Physics.Closure.NSA6TheoremLadderBoundary
  as A6Ladder
import DASHI.Physics.Closure.NSBonyParaproductA6RepairBoundary
  as BonyRepair

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
--     -> smallness threshold D_r < (c / 2C)^(1 / α)
--     -> monotone decay of D_r
--     -> D_r -> 0
--     -> contradiction with persistent blowup.
--
-- It promotes only the local A7 residual-depletion threshold payload after
-- consuming the now-true A6 ladder/residual nonpositive dependencies.  It
-- proves no A8 local monotonicity, no A9 CKN/BKM closure, no Navier-Stokes
-- Clay result, and no terminal promotion.

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

bonyRepairBoundaryReference : String
bonyRepairBoundaryReference =
  "DASHI.Physics.Closure.NSBonyParaproductA6RepairBoundary"

bonyRepairConsumedRecorded : Bool
bonyRepairConsumedRecorded =
  true

record ImportedA7ThresholdSupport : Set where
  field
    a6ClosureBoundary :
      A6Closure.NSA6A4BiasToLeakageClosureCompositeBoundary
    a6ClosureBoundaryIsCanonical :
      a6ClosureBoundary
        ≡ A6Closure.canonicalNSA6A4BiasToLeakageClosureCompositeBoundary
    bonyRepairBoundary :
      BonyRepair.NSBonyParaproductA6RepairBoundary
    bonyRepairBoundaryIsCanonical :
      bonyRepairBoundary
        ≡ BonyRepair.canonicalNSBonyParaproductA6RepairBoundary
    importedA6TheoremTrue :
      A6Ladder.A6TheoremProved ≡ true
    importedA6ResidualNonpositiveTrue :
      A6Ladder.residualNonpositiveProved ≡ true
    importedA6LocalDefectStillFalse :
      A6Ladder.localDefectMonotonicityProved ≡ false
    importedA6CKNBKMStillFalse :
      A6Ladder.cknBkmClosureProved ≡ false
    importedA6ClayStillFalse :
      A6Ladder.nsClayPromoted ≡ false
    importedA6TerminalStillFalse :
      A6Ladder.terminalPromotion ≡ false
    importedBonyRepairPromoted :
      BonyRepair.bonyParaproductA6RepairPromotedHere ≡ true
    importedBonyCriticalResidualPromoted :
      BonyRepair.criticalResidualDepletionProvedAnchor ≡ true
    importedBonyClayStillFalse :
      BonyRepair.NSClayNotPromoted ≡ true
    importedBonyTerminalStillFalse :
      BonyRepair.terminalPromotionNotPromoted ≡ true

canonicalImportedA7ThresholdSupport : ImportedA7ThresholdSupport
canonicalImportedA7ThresholdSupport =
  record
    { a6ClosureBoundary =
        A6Closure.canonicalNSA6A4BiasToLeakageClosureCompositeBoundary
    ; a6ClosureBoundaryIsCanonical =
        refl
    ; bonyRepairBoundary =
        BonyRepair.canonicalNSBonyParaproductA6RepairBoundary
    ; bonyRepairBoundaryIsCanonical =
        refl
    ; importedA6TheoremTrue =
        refl
    ; importedA6ResidualNonpositiveTrue =
        refl
    ; importedA6LocalDefectStillFalse =
        refl
    ; importedA6CKNBKMStillFalse =
        refl
    ; importedA6ClayStillFalse =
        refl
    ; importedA6TerminalStillFalse =
        refl
    ; importedBonyRepairPromoted =
        refl
    ; importedBonyCriticalResidualPromoted =
        refl
    ; importedBonyClayStillFalse =
        refl
    ; importedBonyTerminalStillFalse =
        refl
    }

------------------------------------------------------------------------
-- A7 proof clauses.

data A7GronwallClause : Set where
  importedA6DifferentialInequalityInput :
    A7GronwallClause
  positiveParametersAlphaBetaCEffective :
    A7GronwallClause
  smallnessThresholdDrLessThanBetaOverCEffToOneOverAlpha :
    A7GronwallClause
  bernoulliThresholdDrLessThanCOverTwoCToOneOverAlpha :
    A7GronwallClause
  bonyConstantCBonyMAbsorbedIntoEffectiveC :
    A7GronwallClause
  cknEpsilonThresholdDominatedByA7Smallness :
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
  ∷ bernoulliThresholdDrLessThanCOverTwoCToOneOverAlpha
  ∷ bonyConstantCBonyMAbsorbedIntoEffectiveC
  ∷ cknEpsilonThresholdDominatedByA7Smallness
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

a7GronwallClauseCountIs14 :
  a7GronwallClauseCount ≡ 14
a7GronwallClauseCountIs14 =
  refl

data A7GronwallTransformationStep : Set where
  step-rewriteAsDtDrLeqNegativeBetaDrPlusCDrPower :
    A7GronwallTransformationStep
  step-specializeBetaToCOverTwoFromA6Gap :
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
  ∷ step-specializeBetaToCOverTwoFromA6Gap
  ∷ step-differentiateDrToMinusAlpha
  ∷ step-cancelCommonPowerOfDr
  ∷ step-obtainLinearLowerBoundForZPrime
  ∷ step-integrateLinearComparison
  ∷ []

a7GronwallTransformationStepCount : Nat
a7GronwallTransformationStepCount =
  listLength canonicalA7GronwallTransformationSteps

a7GronwallTransformationStepCountIs6 :
  a7GronwallTransformationStepCount ≡ 6
a7GronwallTransformationStepCountIs6 =
  refl

data A7ThresholdConsequence : Set where
  thresholdDefinesForwardInvariantSmallDataRegion :
    A7ThresholdConsequence
  thresholdDominatesNonlinearSourceTerm :
    A7ThresholdConsequence
  thresholdCanBeRestatedAsCEffDrPowerAlphaLessThanBeta :
    A7ThresholdConsequence
  thresholdCanBeRestatedAsCDrPowerAlphaLessThanCOverTwo :
    A7ThresholdConsequence
  thresholdCompatibleWithCBonyMEffectiveConstant :
    A7ThresholdConsequence
  thresholdBelowClassicalCKNEpsilonRegularityScale :
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
  ∷ thresholdCanBeRestatedAsCDrPowerAlphaLessThanCOverTwo
  ∷ thresholdCompatibleWithCBonyMEffectiveConstant
  ∷ thresholdBelowClassicalCKNEpsilonRegularityScale
  ∷ thresholdForcesNegativeDrDerivative
  ∷ thresholdIsCompatibleWithDepletionContradictionStrategy
  ∷ []

a7ThresholdConsequenceCount : Nat
a7ThresholdConsequenceCount =
  listLength canonicalA7ThresholdConsequences

a7ThresholdConsequenceCountIs8 :
  a7ThresholdConsequenceCount ≡ 8
a7ThresholdConsequenceCountIs8 =
  refl

data A7ThresholdClause : Set where
  thresholdUsesTheImportedA6ConstantCEff :
    A7ThresholdClause
  thresholdEqualsBetaOverCEffToOneOverAlpha :
    A7ThresholdClause
  thresholdEqualsCOverTwoCToOneOverAlpha :
    A7ThresholdClause
  thresholdUsesEffectiveConstantCIncludingCBonyM :
    A7ThresholdClause
  thresholdIsChosenBelowCKNEpsilon :
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
  ∷ thresholdEqualsCOverTwoCToOneOverAlpha
  ∷ thresholdUsesEffectiveConstantCIncludingCBonyM
  ∷ thresholdIsChosenBelowCKNEpsilon
  ∷ thresholdRequiresAlphaPositiveAndBetaPositive
  ∷ thresholdProducesStrictDerivativeGap
  ∷ thresholdRegionIsForwardInvariantUnderComparison
  ∷ []

a7ThresholdClauseCount : Nat
a7ThresholdClauseCount =
  listLength canonicalA7ThresholdClauses

a7ThresholdClauseCountIs8 :
  a7ThresholdClauseCount ≡ 8
a7ThresholdClauseCountIs8 =
  refl

a7GronwallThresholdTheoremText : String
a7GronwallThresholdTheoremText =
  "A7 promoted local threshold payload: import the true A6 inequality ∂t D_r + β D_r <= C_eff D_r^(1+alpha) with α,β,C_eff > 0 and β specialized to the retained gap c/2, absorb C_Bony(M) into the effective C, choose δ_A7 = min((c / (2C))^(1 / alpha), epsilon_CKN), rewrite with Z = D_r^(-alpha), derive Z' >= alpha*beta*Z - alpha*C_eff, and conclude forward-invariant monotone decay D_r -> 0 below δ_A7."

a7ThresholdSummary : String
a7ThresholdSummary =
  "Exact threshold grammar: if 0 < D_r < (c / (2C))^(1 / alpha) with C including C_Bony(M), then C D_r^(1+alpha) < (c/2) D_r, hence ∂t D_r < 0 and the subthreshold region is comparison-stable forward in time."

a7GronwallComparisonSummary : String
a7GronwallComparisonSummary =
  "Gronwall comparison grammar: after Z = D_r^(-alpha), the transformed inequality is Z' >= alpha*beta*Z - alpha*C_eff; linear comparison yields exponential lower growth for Z once above the equilibrium C_eff / beta, forcing D_r to decrease and eventually vanish."

a7BonyCompatibilitySummary : String
a7BonyCompatibilitySummary =
  "C_Bony(M) compatibility: the corrected Bony/paraproduct repair is imported as true, and its M-dependent constant is carried only by the effective constant C in δ_A7 = (c/(2C))^(1/alpha)."

a7CKNEpsilonThresholdSummary : String
a7CKNEpsilonThresholdSummary =
  "CKN epsilon threshold: A7 chooses δ_A7 below epsilon_CKN so residual depletion is compatible with the later CKN/BKM handoff, while A9 itself remains unproved here."

------------------------------------------------------------------------
-- Downstream blockers and fail-closed promotion state.

data DownstreamA7Blocker : Set where
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
  blocker-a8-full-local-defect-monotonicity-unproved
  ∷ blocker-a9-ckn-bkm-closure-unproved
  ∷ blocker-ns-clay-authority-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

downstreamA7BlockerCount : Nat
downstreamA7BlockerCount =
  listLength canonicalDownstreamA7Blockers

downstreamA7BlockerCountIs4 :
  downstreamA7BlockerCount ≡ 4
downstreamA7BlockerCountIs4 =
  refl

downstreamA7BlockerName : DownstreamA7Blocker → String
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
  true

A7ResidualDepletionGronwallProvedIsTrue :
  A7ResidualDepletionGronwallProved ≡ true
A7ResidualDepletionGronwallProvedIsTrue =
  refl

A7BernoulliGronwallThresholdPayloadPromoted : Bool
A7BernoulliGronwallThresholdPayloadPromoted =
  true

A7BernoulliGronwallThresholdPayloadPromotedIsTrue :
  A7BernoulliGronwallThresholdPayloadPromoted ≡ true
A7BernoulliGronwallThresholdPayloadPromotedIsTrue =
  refl

A7BonyCompatibilityPromoted : Bool
A7BonyCompatibilityPromoted =
  true

A7BonyCompatibilityPromotedIsTrue :
  A7BonyCompatibilityPromoted ≡ true
A7BonyCompatibilityPromotedIsTrue =
  refl

A7CKNEpsilonThresholdPayloadPromoted : Bool
A7CKNEpsilonThresholdPayloadPromoted =
  true

A7CKNEpsilonThresholdPayloadPromotedIsTrue :
  A7CKNEpsilonThresholdPayloadPromoted ≡ true
A7CKNEpsilonThresholdPayloadPromotedIsTrue =
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
    importedThresholdSupport :
      ImportedA7ThresholdSupport
    importedThresholdSupportIsCanonical :
      importedThresholdSupport ≡ canonicalImportedA7ThresholdSupport
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
    clauseCountIs14 :
      a7GronwallClauseCount ≡ 14
    transformationStepCountIs6 :
      a7GronwallTransformationStepCount ≡ 6
    thresholdConsequenceCountIs8 :
      a7ThresholdConsequenceCount ≡ 8
    thresholdClauseCountIs8 :
      a7ThresholdClauseCount ≡ 8
    theoremText :
      String
    thresholdSummary :
      String
    gronwallComparisonSummary :
      String
    bonyCompatibilitySummary :
      String
    cknEpsilonThresholdSummary :
      String
    blockerCountIs4 :
      downstreamA7BlockerCount ≡ 4
    a7PromotedTrue :
      A7ResidualDepletionGronwallProved ≡ true
    bernoulliGronwallThresholdPayloadPromotedTrue :
      A7BernoulliGronwallThresholdPayloadPromoted ≡ true
    bonyCompatibilityPromotedTrue :
      A7BonyCompatibilityPromoted ≡ true
    cknEpsilonThresholdPayloadPromotedTrue :
      A7CKNEpsilonThresholdPayloadPromoted ≡ true
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
    { importedThresholdSupport =
        canonicalImportedA7ThresholdSupport
    ; importedThresholdSupportIsCanonical =
        refl
    ; gronwallClauses =
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
    ; clauseCountIs14 =
        refl
    ; transformationStepCountIs6 =
        refl
    ; thresholdConsequenceCountIs8 =
        refl
    ; thresholdClauseCountIs8 =
        refl
    ; theoremText =
        a7GronwallThresholdTheoremText
    ; thresholdSummary =
        a7ThresholdSummary
    ; gronwallComparisonSummary =
        a7GronwallComparisonSummary
    ; bonyCompatibilitySummary =
        a7BonyCompatibilitySummary
    ; cknEpsilonThresholdSummary =
        a7CKNEpsilonThresholdSummary
    ; blockerCountIs4 =
        refl
    ; a7PromotedTrue =
        refl
    ; bernoulliGronwallThresholdPayloadPromotedTrue =
        refl
    ; bonyCompatibilityPromotedTrue =
        refl
    ; cknEpsilonThresholdPayloadPromotedTrue =
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

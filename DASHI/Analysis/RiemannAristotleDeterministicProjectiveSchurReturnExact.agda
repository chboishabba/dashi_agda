module DASHI.Analysis.RiemannAristotleDeterministicProjectiveSchurReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record DeterministicProjectiveSchurReturn : Set where
  constructor deterministic-projective-schur-return
  field
    sourceImplementedInLean : Bool
    sourceImplementedInLeanIsTrue : sourceImplementedInLean ≡ true
    machineCheckedInLeanForThisReturn : Bool
    machineCheckedInLeanForThisReturnIsTrue : machineCheckedInLeanForThisReturn ≡ true
    aggregateLeanBuildJobsReported : String
    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false
    primeProjectiveDebtInHighOrdinateLane : Bool
    primeProjectiveDebtInHighOrdinateLaneIsFalse : primeProjectiveDebtInHighOrdinateLane ≡ false
    gammaResidualDebtAfterSchur : Bool
    gammaResidualDebtAfterSchurIsFalse : gammaResidualDebtAfterSchur ≡ false
    poleResidualDebtAfterSchur : Bool
    poleResidualDebtAfterSchurIsFalse : poleResidualDebtAfterSchur ≡ false
    deterministicNuisanceIndependenceConstructed : Bool
    deterministicNuisanceIndependenceConstructedIsFalse : deterministicNuisanceIndependenceConstructed ≡ false
    targetClusterSurvivalAfterDeterministicSchurConstructed : Bool
    targetClusterSurvivalAfterDeterministicSchurConstructedIsFalse : targetClusterSurvivalAfterDeterministicSchurConstructed ≡ false
    boundedReading : String

open DeterministicProjectiveSchurReturn public

canonicalDeterministicProjectiveSchurReturn : DeterministicProjectiveSchurReturn
canonicalDeterministicProjectiveSchurReturn =
  deterministic-projective-schur-return
    true refl
    true refl
    "8883"
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The supplied aggregate Lean build imports LiteralWeilDeterministicProjectiveSchur, so the deterministic projective Schur compiler is now kernel-checked in the current return. Lean proof terms are not transported into Agda. The remaining construction socket is analytic: build the short three-taper family with deterministic nuisance rank two and surviving off-line cluster margin."

record DeterministicProjectiveSchurBoundary : Set where
  constructor deterministic-projective-schur-boundary
  field
    separatePositiveGammaBudgetSufficientUniformlyNearCriticalLine : Bool
    separatePositiveGammaBudgetSufficientUniformlyNearCriticalLineIsFalse : separatePositiveGammaBudgetSufficientUniformlyNearCriticalLine ≡ false
    separatePositivePoleBudgetSufficientUniformlyNearCriticalLine : Bool
    separatePositivePoleBudgetSufficientUniformlyNearCriticalLineIsFalse : separatePositivePoleBudgetSufficientUniformlyNearCriticalLine ≡ false
    exactDeterministicEliminationPreferred : Bool
    exactDeterministicEliminationPreferredIsTrue : exactDeterministicEliminationPreferred ≡ true

canonicalDeterministicProjectiveSchurBoundary : DeterministicProjectiveSchurBoundary
canonicalDeterministicProjectiveSchurBoundary =
  deterministic-projective-schur-boundary false refl false refl true refl
